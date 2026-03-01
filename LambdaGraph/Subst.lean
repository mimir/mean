import LambdaGraph.Nest

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
noncomputable def Expr.subst (p : Program) (e : Expr) (vm : VarMap p.size)
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
          let ⟨p₂, f', fm₂, hsize₂, hum₂⟩ := p.fn[m].subst p₁ vm₁ fm₁
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
      let ⟨p₁, f', fm₁, hsize₁, hum₁⟩ := f.subst p vm fm
      let ⟨p₂, e', fm₂, hsize₂, hum₂⟩ := e.subst p₁ vm.extend fm₁
      ⟨p₂, f'.app e', fm₂, by omega, by omega⟩
    | bool b => ⟨p, bool b, fm, Nat.le_refl _, Nat.le_refl _⟩
    | cond c et ef =>
      let ⟨p₁, c', fm₁, hsize₁, hum₁⟩ := c.subst p vm fm
      let vm₁ := vm.extend
      let ⟨p₂, et', fm₂, hsize₂, hum₂⟩ := et.subst p₁ vm₁ fm₁
      let ⟨p₃, ef', fm₃, hsize₃, hum₃⟩ := ef.subst p₂ vm₁.extend fm₂
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

/-- Substitutes a value for a variable in a computation. -/
noncomputable def Computation.subst (p : Computation) (n : Nat) (v : Expr) :
    Computation :=
  let ⟨p', e', _, _, _⟩ := p.expr.subst p.toProgram (.mk _ n v) (.mk _)
  ⟨p', e'⟩

theorem Program.subst_ty_eq_of_lt {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, fm', hsize, _⟩ := e.subst p vm fm
    p'.ty[n] = p.ty[n] := by
  fun_induction Expr.subst <;> dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst p₂
    grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    have hp₁ : p₁ = (f.subst p vm fm).program := by grind
    have hp₂ : p₂ = (e.subst p₁ vm.extend fm₁).program := by grind
    subst p₁ p₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    have hp₁ : p₁ = (c.subst p vm fm).program := by grind
    have hp₂ : p₂ = (et.subst p₁ vm.extend fm₁).program := by grind
    have hp₃ : p₃ = (ef.subst p₂ vm₁.extend fm₂).program := by grind
    subst p₁ p₂ p₃
    grind

theorem Program.subst_fn_eq_of_lt {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, _, hsize, _⟩ := (e.subst p vm fm)
    p'.fn[n] = p.fn[n] := by
  fun_induction Expr.subst <;>
    first | grind
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst p₂
    grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    have hp₁ : p₁ = (f.subst p vm fm).program := by grind
    have hp₂ : p₂ = (e.subst p₁ vm.extend fm₁).program := by grind
    subst p₁ p₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    have hp₁ : p₁ = (c.subst p vm fm).program := by grind
    have hp₂ : p₂ = (et.subst p₁ vm.extend fm₁).program := by grind
    have hp₃ : p₃ = (ef.subst p₂ vm₁.extend fm₂).program := by grind
    subst p₁ p₂ p₃
    grind

theorem Expr.types_in_subst_of_types {p : Program} {e₁ e₂ : Expr} {t : Ty}
    {vm : VarMap p.size} {fm : FunMap p.size} (ht : p ⊢ e₁ : t) :
    (e₂.subst p vm fm).program ⊢ e₁ : t := by
  induction ht with
    first | constructor <;> assumption
          | rw [← Program.subst_ty_eq_of_lt]; constructor

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
    vm.extend.Types (e.subst p vm fm).program := by
  intro i hi
  simp only [VarMap.extend, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · apply Expr.types_in_subst_of_types
    rw [Program.subst_ty_eq_of_lt]
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
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    fm'.Types p' := by
  dsimp only
  fun_induction Expr.subst <;>
    first | grind
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst p₂
    have hfm₂ : fm₂ = (p.fn[m].subst p₁ vm₁ fm₁).funMap := by grind
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
    let ⟨p', e', _, _, _⟩ := e.subst p vm fm
    p' ⊢ e' : t := by
  fun_induction subst generalizing t <;> dsimp only at *
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
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst hp₂
    have : p.ty[m] = p₃.ty[p.size] := by grind [Program.subst_ty_eq_of_lt]
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
    ⊢ (e.subst p vm fm).program := by
  fun_induction Expr.subst <;>
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
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst p₂
    have ht₂ : ⊢ _ := ih ht₁ hvm₁ hfm₁
    intro i hi
    simp only [p₃]
    by_cases m' = i
    · subst i
      have hf' : f' = (p.fn[m].subst p₁ vm₁ fm₁).expr := by grind
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
    {fm : FunMap p.size} : (e.subst p vm fm).funMap.Extends fm := by
  fun_induction Expr.subst <;>
    try solve | constructor <;> simp_all
              | grind [extends_update]

def Expr.NoSubst {n : Nat} (e : Expr) (fm : FunMap n) : Prop :=
  ∀ ⦃m r⦄ (_ : m < n), e.Local (fm[m].getD m) r → fm[m].getD m = m

theorem Expr.noSubst_mk {n : Nat} {e : Expr} : e.NoSubst (.mk n) := by
  grind [Expr.NoSubst]

@[simp, grind =]
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

@[simp, grind =]
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

structure FunMap.Valid {n : Nat} (fm : FunMap n) : Prop where
  lt : ∀ {m} (_ : m < n), fm[m].getD m < n
  inj : ∀ {m k} (_ : m < n) (_ : k < n),
    fm[m].getD m ≠ m → fm[k].getD k ≠ k → fm[m].getD m = fm[k].getD k → m = k
  idem : ∀ {m} (_ : m < n),
    (fm[fm[m].getD m]'(lt _)).getD (fm[m].getD m) = fm[m].getD m
  eq_none : ∀ {m k} (_ : m < n) (_ : k < n),
    fm[m] = none → fm[k].getD k ≠ m

grind_pattern FunMap.Valid.lt =>
  fm.Valid, m < n, fm[m].getD m
  where m =/= Option.getD _ _

attribute [grind =] FunMap.Valid.idem

theorem FunMap.valid_mk {n : Nat} : (mk n).Valid := by
  constructor <;> grind

theorem FunMap.valid_update {n : Nat} {fm : FunMap n} {i : Nat}
    (hi : i < n) (hfm : fm[i] = none) (h : fm.Valid) :
    (fm.update i hi).Valid := by
  constructor
  case lt =>
    intro k hk
    by_cases k = n
    · simp [*]
    · replace hk : k < n := by lia
      grind
  case inj =>
    intro m k hm hk hmm' hkk' heq
    replace hm : m < n := by grind
    replace hk : k < n := by grind
    have := h.inj hm hk
    grind
  case idem =>
    intro m hm
    by_cases m = n
    · simp [*]
    · replace hm : m < n := by lia
      have := h.eq_none hi hm hfm
      grind
  case eq_none =>
    intro m k hm hk heq
    replace hm : m < n := by grind
    have him : i ≠ m := by grind
    simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, hm, him] at heq
    by_cases k = n
    · grind
    · replace hk : k < n := by lia
      have := h.eq_none hm hk heq
      grind

theorem FunMap.valid_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (h : fm.Valid) : (e.subst p vm fm).funMap.Valid := by
  fun_induction Expr.subst <;> try simpa using h
  next p vm fm m hm hfm m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum hf ih =>
    rw [hs₂] at ih
    exact ih (valid_update hm hfm h)
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ hf ihf ihe =>
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    exact ihe (ihf h)
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ hf ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    exact ihef (ihet (ihc h))

grind_pattern FunMap.valid_subst => (e.subst p vm fm).funMap

structure VarMap.Valid {n : Nat} (vm : VarMap n) (fm : FunMap n) : Prop where
  bounded : ∀ {m} (_ : m < n), vm[m].Bounded n
  localProvenance : ∀ {m} (_ : m < n),
    fm[m].getD m ≠ m → fm.LocalProvenance (.var m) vm[m] none
  noSubst : ∀ {m} (_ : m < n),
    fm[m].getD m = m → vm[m] ≠ .var m → vm[m].NoSubst fm

attribute [grind! .] VarMap.Valid.bounded

theorem VarMap.valid_mk {n m : Nat} {v : Expr} (hv : v.Bounded n) :
    (mk n m v).Valid (.mk n) := by
  constructor <;> grind [Expr.NoSubst]

theorem VarMap.valid_update {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {i : Nat} (hi : i < p.size) (hvm : vm.Valid fm)
    (hfm : fm.Valid) : (vm.update i hi).Valid (fm.update i hi) := by
  constructor
  case bounded =>
    intro k hk
    by_cases k = p.size
    · simp [*]
    · by_cases i = k
      · subst k
        simp [*]
      · replace hk : k < p.size := by lia
        simpa [*] using Expr.bounded_of_ge (by lia) (hvm.bounded hk)
  case localProvenance =>
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
      apply hvm.localProvenance <;> simp_all
  case noSubst =>
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
      refine hvm.noSubst hm ?_ ?_ hn hl <;> simp_all

theorem VarMap.valid_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) :
    vm.extend.Valid (e.subst p vm fm).funMap := by
  fun_induction Expr.subst <;> try simpa [extend_eq]
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have hvm₁ : vm₁.Valid fm₁ := valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm heq hfm
    have hvm₂ : vm₁.extend.Valid fm₂ := ih hvm₁ hfm₁
    have hfm₂ : fm₂.Valid := by grind
    have hext₁ := FunMap.extends_update hm heq
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hext := FunMap.extends_trans hext₁ hext₂
    constructor
    case bounded =>
      intro k hk
      by_cases hk : k < p.size
      · simp [*]
        exact Expr.bounded_of_ge (by lia) (hvm.bounded hk)
      · simp_all
    case localProvenance =>
      intro k hk hkk' l r hl hll' hlc
      by_cases k < p.size
      · simp only [VarMap.getElem_extend_lt, *] at hlc
        by_cases m = k
        · subst k
          have hl' : fm₂[l].getD l < p.size := hvm.bounded hm hlc
          obtain ⟨hl, heq⟩ := hext.eq_of_lt hl hl'
          rw [heq] at hlc
          by_cases hvmm : vm[m] = .var m
          · grind
          · have := hvm.noSubst hm (by simp [*]) hvmm hl hlc
            grind
        · exact hvm₂.localProvenance hk hkk' hl hll' (by grind)
      · exact hvm₂.localProvenance hk hkk' hl hll' (by grind)
    case noSubst =>
      intro k hk hkk' hne
      by_cases hk : k < p.size
      · have hkk' : fm[k].getD k = k := by grind
        simp only [VarMap.getElem_extend_lt, *] at hne ⊢
        intro l r hl hlc
        by_cases hll'₂ : fm₂[l].getD l = l
        · exact hll'₂
        · have hl' : fm₂[l].getD l < p.size := hvm.bounded hk hlc
          obtain ⟨hl, heq⟩ := hext.eq_of_lt hl hl'
          rw [heq] at hlc
          have := hvm.noSubst hk hkk' hne hl hlc
          grind
      · simp_all
  next => grind
  next => grind

grind_pattern VarMap.valid_subst =>
  vm.extend (n' := (e.subst p vm fm).program.size)

theorem Expr.validRefs_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (he : e.ValidRefs p) :
    let ⟨p', e', _, _, _⟩ := e.subst p vm fm
    e'.ValidRefs p' := by
  fun_induction subst
  next => simp [*]
  next => simp_all [hvm.bounded]
  next => grind
  next p vm fm m hm m' hfm h =>
    have hfmm : fm[m].getD m = m' := by simp [*]
    grind
  next => grind
  next =>
    grind [bounded_of_ge, noSubst_of_extends_of_noSubst]
  next => simp
  next =>
    grind [bounded_of_ge, noSubst_of_extends_of_noSubst]

theorem Expr.localProvenance_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) :
    let ⟨_, e', fm', _, _⟩ := e.subst p vm fm
    fm'.LocalProvenance e e' none := by
  fun_induction Expr.subst
  next p e vm fm h =>
    intro n r hn hnn' hl
    simpa [hns hn hl] using hl
  next p vm fm m h =>
    intro n r hn hnn' hl
    simp only [Expr.bounded_var_iff] at he
    simp only [he, getElem?_pos, Option.getD_some] at hl
    by_cases hmm' : fm[m].getD m = m
    · simp only [Classical.not_forall] at h
      obtain ⟨k, hk, hf, hne⟩ := h
      have .var := hf
      have := hvm.noSubst he hmm' hne hn hl
      contradiction
    · exact hvm.localProvenance he hmm' hn hnn' hl
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm heq hfm
    have hfm₂ : fm₂.Valid := by grind
    have hext₂ : fm₂.Extends fm₁ := by grind
    intro n r hn hnn' hl
    subst f''
    simp only [Expr.local_fn_iff] at hl
    obtain ⟨hr, hmn'⟩ := hl
    have : fm₂[m].getD m = m' := by
      rw [hext₂.eq (by lia) (by grind)]
      simp [fm₁, m']
    rw [← this] at hmn'
    have : m = n := hfm₂.inj (by lia) hn (by grind) hnn' hmn'
    simp [*]
  next p vm fm m hm m' hfm h =>
    have hfmm : fm[m].getD m = m' := by simp [*]
    intro n r hn hnn' hl
    have hm' := hfm.lt hm
    by_cases hmm' : m = m'
    · have := hns hn (hmm' ▸ hl)
      contradiction
    · grind [hfm.inj]
  next => grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    dsimp only at *
    have hvm₁ : vm.extend.Valid fm₁ := by grind
    have hfm₁ : fm₁.Valid := by grind
    obtain ⟨hvf, hve⟩ := Expr.bounded_app_iff.mp he
    obtain ⟨hnsf, hnse⟩ := Expr.noSubst_app_iff.mp hns
    have hf' := ihf hvm hfm hvf hnsf
    have he' := ihe hvm₁ hfm₁ (bounded_of_ge hsize₁ hve)
      (noSubst_of_extends_of_noSubst (by grind) (by grind) hnse)
    intro n r hn hnn' hl
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hvf' : f'.ValidRefs p₁ := by grind [validRefs_subst]
    obtain hl | hl := Expr.local_app_iff.mp hl
    · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hn (hvf' hl)
      rw [heq] at hl
      have := hf' hn (by grind) hl
      grind
    · have := he' hn hnn' hl
      grind
  next p vm fm b h => simp [FunMap.LocalProvenance]
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    have hvm₁ : vm₁.Valid fm₁ := by grind
    have hfm₁ : fm₁.Valid := by grind
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind
    have hfm₂ : fm₂.Valid := by grind
    obtain ⟨hvc, hvet, hvef⟩ := Expr.bounded_cond_iff.mp he
    obtain ⟨hnsc, hnset, hnsef⟩ := Expr.noSubst_cond_iff.mp hns
    have hc' := ihc hvm hfm hvc hnsc
    have het' := ihet hvm₁ hfm₁ (bounded_of_ge hsize₁ hvet)
      (noSubst_of_extends_of_noSubst (by grind) (by grind) hnset)
    have hef' := ihef hvm₂ hfm₂ (bounded_of_ge (by lia) hvef)
      (noSubst_of_extends_of_noSubst (by grind) (by grind) hnsef)
    intro n r hn hnn' hl
    have hext₁ : fm₃.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    have hvc' : c'.ValidRefs p₁ := by grind [validRefs_subst]
    have hvet' : et'.ValidRefs p₂ := by
      grind [validRefs_subst, bounded_of_ge, noSubst_of_extends_of_noSubst]
    obtain hl | hl | hl := Expr.local_cond_iff.mp hl
    · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hn (hvc' hl)
      rw [heq] at hl
      have := hc' hn (by lia) hl
      grind
    · replace ⟨hn, heq⟩ := hext₂.eq_of_lt hn (hvet' hl)
      rw [heq] at hl
      have := het' hn (by lia) hl
      grind
    · have := hef' hn hnn' hl
      grind

theorem Program.validRefs_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (hp : p.ValidRefs) : (e.subst p vm fm).program.ValidRefs := by
  fun_induction Expr.subst <;> try simpa using hp
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm heq hfm
    have hp₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
    have hf' : f'.ValidRefs p₂ := by
      have : p.fn[m].ValidRefs p₁ := Expr.validRefs_in_push (hp hm)
      grind [Expr.validRefs_subst]
    exact validRefs_setBody hsize₂ hp₂ hf'
  next => grind
  next => grind

structure Program.ValidSubst (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) where
  fn_localProvenance : ∀ {m m'} (_ : m < p.size) (_ : m' < p.size),
    m' = fm[m].getD m → m' ≠ m → fm.LocalProvenance p.fn[m] p.fn[m'] m
  fn_noSubst : ∀ {m} (_ : m < p.size), fm[m] = none → p.fn[m].NoSubst fm

theorem Program.validSubst_mk {p : Program} {n : Nat} {v : Expr} :
    p.ValidSubst (.mk _ n v) (.mk _) := by
  constructor <;> grind

theorem Program.validSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {i : Nat} (hi : i < p.size) (hfm : fm.Valid)
    (hp : p.ValidRefs) (h : p.ValidSubst vm fm) :
    (p.push (.recurse p.size) p.ty[i]).ValidSubst
      (vm.update i hi) (fm.update i hi) := by
  constructor
  case fn_localProvenance =>
    intro m m' hm hm' hfmm hmm' n r hn hnn' hl
    by_cases hnm : n = m
    · simp [*]
    · right
      have : m ≠ p.size := by
        rintro rfl
        simp [*] at hmm'
      have : n ≠ p.size := by
        rintro rfl
        simp at hnn'
      replace hm : m < p.size := by lia
      replace hn : n < p.size := by lia
      have hm' := hfm.lt hm
      have hn' := hfm.lt hn
      have him : i ≠ m := by grind
      have hin : i ≠ n := by grind
      simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, Vector.getElem_push_lt, hm,
        him, hn, hin, hfmm, hm'] at hmm' hnn' hl
      have := h.fn_localProvenance hm hm' rfl hmm' hn hnn' hl
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

theorem Program.validSubst_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (he : e.ValidRefs p) (hns : e.NoSubst fm) :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    p'.ValidSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hvalid
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm heq hfm
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind [VarMap.valid_subst]
    have hfm₂ : fm₂.Valid := by grind
    have hp₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
      (validSubst_push_recurse hm hfm hp hvalid)
      (Expr.validRefs_in_push (hp hm))
      (Expr.noSubst_of_extends_of_noSubst (by grind)
        (FunMap.extends_update hm heq) (hvalid.fn_noSubst hm heq))
    have hprov : fm₂.LocalProvenance p.fn[m] f' none := by
      grind [Expr.localProvenance_subst, Expr.noSubst_of_extends_of_noSubst,
        FunMap.extends_update, hvalid.fn_noSubst, Expr.bounded_of_ge]
    have hext₁ := FunMap.extends_update hm heq
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hext := FunMap.extends_trans hext₁ hext₂
    constructor
    case fn_localProvenance =>
      intro n n' hn hn' hfmn hnn' k r hk hkk' hl
      subst n'
      have hfmm : fm₂[m].getD m = m' := by grind [hext₂.eq]
      by_cases hnm : m = n
      · subst n
        simp only [Vector.getElem_set_self, p₃, hfmm] at hl
        replace hl := hprov hk hkk' hl
        simp only [reduceCtorEq, false_or] at hl
        rw [hfmm] at hnn'
        have heq : p₂.fn[m] = p.fn[m] := by
          have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [subst_fn_eq_of_lt (by lia)]
          simp [p₁, hm]
        simp [p₃, *]
      · have hnm' : fm₂[n].getD n ≠ m' := by
          intro heq
          rw [← heq] at hfmm
          have := hfm₂.inj (by lia) hn (by lia) (by grind) hfmm
          contradiction
        simp only [ne_eq, not_false_eq_true, Ne.symm, Vector.getElem_set_ne, p₃, hnm'] at hl
        have hne : m' ≠ n := by grind
        cases hp₂.fn_localProvenance hn hn' rfl hnn' hk hkk' hl <;> simp [p₃, *]
    case fn_noSubst =>
      intro n hn hfm' k r hk hl
      replace ⟨hn, hfm'⟩ := hext.eq_none hn hfm'
      have hnm' : m' ≠ n := by grind
      have heq : p₃.fn[n] = p.fn[n] := by
        simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, p₃, hnm']
        have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
        subst p₂
        rw [subst_fn_eq_of_lt (by lia)]
        simp [p₁, *]
      rw [heq] at hl
      have hk' := hp hn hl
      obtain ⟨hk, heq⟩ := hext.eq_of_lt hk hk'
      rw [heq] at hl ⊢
      exact hvalid.fn_noSubst hn hfm' hk hl
  next =>
    grind [validRefs_subst, Expr.bounded_of_ge, Expr.noSubst_of_extends_of_noSubst]
  next =>
    grind [validRefs_subst, Expr.bounded_of_ge, Expr.noSubst_of_extends_of_noSubst]

theorem Program.exists_of_ge_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : fm.Valid) {n' : Nat}
    (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    n' < p'.size → ∃ (n : Nat) (_ : n < p.size), n' = fm'[n].getD n := by
  fun_induction Expr.subst generalizing n' <;> try grind
  next p vm fm m hm hfm m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum hf ih =>
    intro hlt
    rw [hs₂] at ih
    dsimp only at *
    have hext : fm₂.Extends fm₁ := by grind
    have hfm' : fm₂[m].getD m = p.size := by
      rw [hext.eq (by lia) (by grind)]
      simp [fm₁]
    grind [FunMap.valid_update]
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ hf ihf ihe =>
    intro hlt
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    dsimp only at *
    have hext₁ : fm₂.Extends fm₁ := by grind
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ hf ihc ihet ihef =>
    intro hlt
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    have h₁ : fm₁.Valid := by grind
    have h₂ : fm₂.Valid := by grind
    have hext₁₂ : fm₂.Extends fm₁ := by grind
    have hext₂₃ : fm₃.Extends fm₂ := by grind
    by_cases n' < p₁.size
    · grind
    · replace hn' : p₁.size ≤ n' := by lia
      by_cases n' < p₂.size
      · obtain ⟨n, hlt, heq⟩ := ihet h₁ hn' ‹_›
        by_cases hn : n < p.size
        · grind
        · replace hn : p.size ≤ n := by lia
          obtain ⟨m, hlt', heq'⟩ := ihc h hn hlt
          have := hext₁₂.eq (show m < p₁.size by lia) (by lia)
          grind
      · replace hn' : p₂.size ≤ n' := by lia
        obtain ⟨n, hlt, heq⟩ := ihef h₂ hn' hlt
        by_cases hn : n < p.size
        · exact ⟨n, hn, heq⟩
        · replace hn : p.size ≤ n := by lia
          by_cases n < p₁.size
          · grind
          · replace hn : p₁.size ≤ n := by lia
            obtain ⟨m, hlt', heq'⟩ := ihet h₁ hn ‹_›
            have := hext₂₃.eq (show m < p₂.size by lia) (by lia)
            grind

theorem Program.lt_size_of_pathWithout_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hp : p.ValidRefs) {m n k : Nat}
    (hm : m < p.size) (hp : m ⟶[(e.subst p vm fm).program, n]* k) :
    k < p.size := by
  induction hp with
  | refl m hm => exact hm
  | step m l k hne hs hp ih =>
    obtain ⟨_, hlf⟩ := hs
    rw [subst_fn_eq_of_lt hm] at hlf
    grind

theorem Program.pathWithout_of_pathWithout_in_subst_of_ge {p : Program}
    {e : Expr} {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' m' k' : Nat}
    (hn' : p.size ≤ n') (hm' : p.size ≤ m') (hk' : p.size ≤ k') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    n' < p'.size → m' < p'.size → k' < p'.size → m' ⟶[p', n']* k' →
      ∃ (n m k : Nat) (hn : n < p.size) (hm : m < p.size) (hk : k < p.size),
        n' = fm'[n].getD n ∧ m' = fm'[m].getD m ∧ k' = fm'[k].getD k ∧ m ⟶[p, n]* k := by
  intro hnlt hmlt hklt hp'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hsize := (e.subst p vm fm).size_ge
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h he hns
  induction hp' with
  | refl m' hne' =>
    obtain ⟨n, hn, hfmn⟩ := exists_of_ge_in_subst hfm hn' hnlt
    obtain ⟨m, hm, hfmm⟩ := exists_of_ge_in_subst hfm hm' hmlt
    have hne : n ≠ m := by grind
    exact ⟨n, m, m, hn, hm, hm, hfmn, hfmm, hfmm, .refl _ hne⟩
  | step m' l' k' hne' hs' hp' ih =>
    obtain ⟨m, hm, hfmm⟩ := exists_of_ge_in_subst hfm hm' hmlt
    have hl' : p.size ≤ l' := by
      false_or_by_contra
      rename_i hl'
      have := lt_size_of_pathWithout_of_lt hp (by simpa using hl') hp'
      lia
    obtain ⟨_, hlf'⟩ := hs'
    have hllt : l' < p'.size := by grind
    have ⟨n, l, k, hn, hl, hk, hfmn, hfml, hfmk, hp⟩ := ih hl' hk' hllt hklt
    have hne : n ≠ m := by grind
    have hlf := h'.fn_localProvenance
      (show m < p'.size by lia) hmlt (by lia) (by grind)
      (show l < p'.size by lia) (by lia) (by simpa [*] using hlf')
    simp only [Option.some.injEq, Program.subst_fn_eq_of_lt hm, p'] at hlf
    obtain heq | hlf := hlf
    · grind
    · refine ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, .step _ _ _ hne ⟨hm, hlf⟩ hp⟩

theorem Program.free_in_fn_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' m' : Nat} (hn' : p.size ≤ n')
    (hm' : p.size ≤ m') (hne' : n' ≠ m') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    ∀ (_ : m' < p'.size), p'.fn[m'].Free p' n' →
      ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
        n' = fm'[n].getD n ∧ m' = fm'[m].getD m ∧ p.fn[m].Free p n := by
  intro hmlt hf'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h he hns
  obtain ⟨k', hklt, hlv', hp'⟩ := (free_in_fn_iff hmlt hne').mp hf'
  have hk' : p.size ≤ k' := by grind [subst_fn_eq_of_lt]
  have hnlt : n' < p'.size := by grind
  obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
    pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp h he hns hn' hm' hk' hnlt hmlt hklt hp'
  have hne : n ≠ m := by grind
  have hlv := h'.fn_localProvenance
    (show k < p'.size by lia) hklt (by lia) (by grind)
    (show n < p'.size by lia) (by lia) (by simpa [hfmn, hfmk] using hlv')
  rw [subst_fn_eq_of_lt hk] at hlv
  simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
  exact ⟨n, m, hn, hm, hfmn, hfmm, (free_in_fn_iff hm hne).mpr ⟨k, hk, hlv, hp⟩⟩

theorem Expr.free_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', e', fm', _, _⟩ := e.subst p vm fm
    e'.Free p' n' → ∃ (n : Nat) (_ : n < p.size),
      n' = fm'[n].getD n ∧ e.Free p n := by
  intro hf
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := Program.validRefs_subst hvm hfm hp
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h he hns
  have hfm' : fm'.Valid := FunMap.valid_subst hfm
  have hlt : n' < p'.size :=
    lt_size_of_free hvp' (validRefs_subst hvm hfm he) hf
  obtain ⟨n, hn, heq⟩ := Program.exists_of_ge_in_subst hfm hn' hlt
  obtain hlv' | ⟨m', k', hk', hlf', hp', hlv'⟩ := free_iff.mp hf
  · refine ⟨n, hn, heq, free_of_localVar ?_⟩
    simpa using localProvenance_subst hvm hfm he hns (by lia) (by lia) (heq ▸ hlv')
  · by_cases hm' : m' < p.size
    · replace hk' := Program.lt_size_of_pathWithout_of_lt hp ‹_› hp'
      grind [Program.subst_fn_eq_of_lt]
    · simp only [Nat.not_lt] at hm'
      have hk' : p.size ≤ k' := by grind [Program.subst_fn_eq_of_lt]
      obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
        Program.pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp h he hns hn' hm' hk'
          ‹_› (validRefs_subst hvm hfm he hlf') ‹_› hp'
      have hlf := localProvenance_subst hvm hfm he hns
        (show m < p'.size by lia) (by lia) (by simpa [*] using hlf')
      simp only [reduceCtorEq, false_or] at hlf
      have hlv := h'.fn_localProvenance
        (show k < p'.size by lia) (show k' < p'.size by grind) (by lia) (by grind)
        (show n < p'.size by lia) (by lia) (by simpa [hfmn, hfmk] using hlv')
      rw [Program.subst_fn_eq_of_lt hk] at hlv
      simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
      exact ⟨n, hn, hfmn, free_iff.mpr <| Or.inr ⟨m, k, hk, hlf, hp, hlv⟩⟩

theorem Program.lt_size_of_free_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidRefs)
    {n m : Nat} (hm : m < p.size) (hne : n ≠ m) :
    let ⟨p', _, _, _, _⟩ := e.subst p vm fm
    p'.fn[m].Free p' n → n < p.size := by
  intro hf
  obtain ⟨k, hk, hlv, hp⟩ := (free_in_fn_iff (by lia) hne).mp hf
  have hk := lt_size_of_pathWithout_of_lt h hm hp
  rw [subst_fn_eq_of_lt hk] at hlv
  exact h hk hlv

theorem Program.lt_size_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidRefs) {n m : Nat}
    (hm : m < p.size) (hnests : n ≻[(e.subst p vm fm).program] m) :
    n < p.size := by
  induction hnests with
  | free m hm' hne hf =>
    exact lt_size_of_free_in_subst_of_lt h hm hne hf
  | step k m hm hne hf hnests ih =>
    exact ih <| lt_size_of_free_in_subst_of_lt h hm hne hf

theorem Expr.validRefs_in_subst {p : Program} {e₁ e₂ : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (he₁ : e₁.ValidRefs p) :
    e₁.ValidRefs (e₂.subst p vm fm).program :=
  let ⟨_, _, _, hsize, _⟩ := (e₂.subst p vm fm)
  bounded_of_ge hsize he₁

theorem Expr.free_of_free_in_subst {p : Program} {e₁ e₂ : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {n : Nat} (hp : p.ValidRefs)
    (he₁ : e₁.ValidRefs p) (hf : e₁.Free (e₂.subst p vm fm).program n) :
    e₁.Free p n := by
  generalize hp' : (e₂.subst p vm fm).program = p' at hf
  induction hf with
    try grind [Free.var, Free.appL, Free.appR, Free.condC, Free.condT, Free.condF]
  | fn k hk' hne hf ih =>
    simp only [bounded_fn_iff] at he₁
    constructor
    · exact hne
    · subst p'
      rw [Program.subst_fn_eq_of_lt he₁] at ih
      exact ih (hp he₁)

theorem Program.nests_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {m n : Nat} (hn : n < p.size)
    (hp : p.ValidRefs) (h : m ≻[(e.subst p vm fm).program] n) :
    m ≻[p] n := by
  generalize hp' : (e.subst p vm fm).program = p' at h
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
    exact Nests.step _ _ hn hne hf (ih (Expr.lt_size_of_free hp (hp hn) hf))

theorem Program.nests_of_nests_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' m' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    n' ≻[p'] m' → ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
      n' = fm'[n].getD n ∧ m' = fm'[m].getD m ∧ n ≻[p] m := by
  intro hnests'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h he hns
  have hfm' : fm'.Valid := FunMap.valid_subst hfm
  induction hnests' with
  | free m' hltm hne' hf' =>
    have hm' : p.size ≤ m' := by
      false_or_by_contra
      rename_i hm'
      simp only [Nat.not_le] at hm'
      have := lt_size_of_free_in_subst_of_lt hp hm' hne' hf'
      lia
    obtain ⟨n, m, hn, hm, hfmn, hfmm, hf⟩ :=
      Program.free_in_fn_of_free_in_subst_of_ge hvm hfm hp h he hns hn' hm' hne' hltm hf'
    have hne : n ≠ m := by grind
    exact ⟨n, m, hn, hm, hfmn, hfmm, .free _ hm hne hf⟩
  | step k' m' hmlt hne' hf' hnests' ih =>
    obtain ⟨n, k, hn, hk, hfmn, hfmk, hnests⟩ := ih
    have hk' : p.size ≤ k' := by
      false_or_by_contra
      rename_i hk'
      have := lt_size_of_nests_in_subst_of_lt hp (by simpa using hk') hnests'
      lia
    have hm' : p.size ≤ m' := by
      false_or_by_contra
      rename_i hm'
      have := lt_size_of_free_in_subst_of_lt hp (by simpa using hm') hne' hf'
      lia
    obtain ⟨l, m, hl, hm, hfml, hfmm, hf⟩ :=
      free_in_fn_of_free_in_subst_of_ge hvm hfm hp h he hns hk' hm' hne' hmlt hf'
    obtain rfl : k = l := hfm'.inj (by lia) (by lia) (by lia) (by lia) (hfmk ▸ hfml)
    have hne : k ≠ m := by grind
    exact ⟨n, m, hn, hm, hfmn, hfmm, .step _ _ hm hne hf hnests⟩

theorem Program.subst_wf {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) (hwf : p.WF) :
    (e.subst p vm fm).program.WF := by
  intro m hnests
  by_cases hm : m < p.size
  · exact hwf <| Program.nests_of_nests_in_subst_of_lt hm hp hnests
  · simp only [Nat.not_lt] at hm
    have hvalid' := Program.validSubst_subst hvm hfm hp h he hns
    have hfm' : (e.subst p vm fm).funMap.Valid := FunMap.valid_subst hfm
    replace ⟨k, l, hk, hl, hfmk, hfml, hnests⟩ :=
      Program.nests_of_nests_in_subst_of_ge hvm hfm hp h he hns hm hnests
    obtain rfl : k = l := hfm'.inj (by lia) (by lia) (by lia) (by lia) (hfmk ▸ hfml)
    exact hwf hnests

namespace Computation

theorem subst_types {c : Computation} {t : Ty} {n : Nat} {v : Expr}
    (hn : n < c.size) (ht : ⊢ c : t) (hv : c.toProgram ⊢ v : c.ty[n]) :
    ⊢ c.subst n v : t := by
  refine ⟨Program.subst_types ht.program_types ?hvm ?hfm,
          Expr.subst_types ht.expr_types ?hvm ?hfm⟩
  · exact VarMap.mk_types hn hv
  · exact FunMap.mk_types

theorem subst_wf {c : Computation} {n : Nat} {v : Expr} (hp : c.ValidRefs)
    (he : c.expr.ValidRefs c.toProgram) (hv : v.ValidRefs c.toProgram)
    (h : c.WF) : (c.subst n v).WF :=
  Program.subst_wf (VarMap.valid_mk hv) FunMap.valid_mk hp
    Program.validSubst_mk he Expr.noSubst_mk h

end Computation
