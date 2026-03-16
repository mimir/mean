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
def FunMap.mk (n : Nat) : FunMap n := Vector.ofFn fun _ => none

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
  ∀ i (_ : i < p.size) m,
    fm[i] = some m → ∃ (_ : m < p.size), p.ty[i] = p.ty[m] ∧ p.ret[i] = p.ret[m]

/--
The result of a substitution.

This contains the updated program and expression, the new function map, as well
as some evidence used in the termination proof.
-/
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

This definition is `noncomputable` as we have not defined a decision procedure
to decide if an expression contains a free substitution variable (but there is
no reason such a procedure could not be implemented).
-/
noncomputable def Expr.subst (p : Program) (e : Expr) (vm : VarMap p.size)
    (fm : FunMap p.size) : SubstResult p fm :=
  if ∀ n (_ : n < p.size), e.Free p n → vm[n] = .var n then
    -- The expression does not contain a free substitution variable, so there is
    -- nothing to do.
    ⟨p, e, fm, Nat.le_refl _, Nat.le_refl _⟩
  else
    match e with
    | var m => ⟨p, vm[m]?.getD (var m), fm, Nat.le_refl _, Nat.le_refl _⟩
    | fn m =>
      if _ : m < p.size then
        match _ : fm[m] with
        | none =>
          -- There is not yet a substitution for this function, so we have to
          -- create a new one.
          let m' := p.size
          let vm₁ := vm.update m
          let fm₁ := fm.update m
          -- Add a new function with a temporary body that is always well-typed.
          let p₁ := p.push (recurse m') p.ty[m] p.ret[m]
          have hsize₁ : p.size ≤ p₁.size := by simp [p₁]
          have hum₁ : fm₁.unmapped < fm.unmapped := by
            simp only [FunMap.unmapped, FunMap.update, reduceCtorEq,
              decide_false, Bool.false_eq_true, not_false_eq_true,
              Vector.countP_push_of_neg, Vector.countP_set, decide_true,
              ↓reduceIte, Nat.add_zero, fm₁, *]
            have : 0 < Vector.countP (fun x => decide (x = none)) fm :=
              Vector.countP_pos_iff.mpr ⟨none, Vector.mem_of_getElem ‹fm[m] = none›, rfl⟩
            omega
          -- Substitute the body to obtain the body for the new function.
          let ⟨p₂, f', fm₂, hsize₂, hum₂⟩ := p.fn[m].subst p₁ vm₁ fm₁
          -- Now put the final function body in place.
          let p₃ := p₂.setBody m' f'
          let e' := fn m'
          have hsize : p.size ≤ p₂.size := by omega
          have hum : fm₂.unmapped ≤ fm.unmapped := by omega
          ⟨p₃, e', fm₂, hsize, hum⟩
        | some m' =>
          -- There is already a substitution for this function, we can reuse it.
          ⟨p, fn m', fm, Nat.le_refl _, Nat.le_refl _⟩
      else
        -- This case is actually impossible, nonexistent functions don't have
        -- free variables.
        ⟨p, fn m, fm, Nat.le_refl _, Nat.le_refl _⟩
    | const c =>
      -- This case is actually impossible, constants don't have free variables.
      ⟨p, const c, fm, Nat.le_refl _, Nat.le_refl _⟩
    | bin k e₁ e₂ =>
      let ⟨p₁, e₁', fm₁, hsize₁, hum₁⟩ := e₁.subst p vm fm
      let ⟨p₂, e₂', fm₂, hsize₂, hum₂⟩ := e₂.subst p₁ vm.extend fm₁
      ⟨p₂, e₁'.bin k e₂', fm₂, by omega, by omega⟩
    | cond c et ef =>
      let ⟨p₁, c', fm₁, hsize₁, hum₁⟩ := c.subst p vm fm
      let vm₁ := vm.extend
      let ⟨p₂, et', fm₂, hsize₂, hum₂⟩ := et.subst p₁ vm₁ fm₁
      let ⟨p₃, ef', fm₃, hsize₃, hum₃⟩ := ef.subst p₂ vm₁.extend fm₂
      ⟨p₃, c'.cond et' ef', fm₃, by omega, by omega⟩
    | proj e i =>
      let ⟨p', e', fm', hsize, hum⟩ := e.subst p vm fm
      ⟨p', e'.proj i, fm', hsize, hum⟩
termination_by (fm.unmapped, e)
decreasing_by all_goals grind

/-- Substitutes a value for a variable in a computation. -/
noncomputable def Computation.subst (p : Computation) (n : Nat) (v : Expr) :
    Computation :=
  let ⟨p', e', _, _, _⟩ := p.expr.subst p.toProgram (.mk _ n v) (.mk _)
  ⟨p', e'⟩

@[simp]
theorem Program.subst_fn_eq_of_lt {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, _, hsize, _⟩ := e.subst p vm fm
    p'.fn[n] = p.fn[n] := by
  fun_induction Expr.subst <;> dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    grind
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂
      h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    grind
  next p vm fm e i p' e' fm' hsize hum hs h ih =>
    rw [hs] at ih
    grind

@[simp]
theorem Program.subst_ty_eq_of_lt {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, _, hsize, _⟩ := e.subst p vm fm
    p'.ty[n] = p.ty[n] := by
  fun_induction Expr.subst <;> dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    grind
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂
      h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    grind
  next p vm fm e i p' e' fm' hsize hum hs h ih =>
    rw [hs] at ih
    grind

@[simp]
theorem Program.subst_ret_eq_of_lt {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, _, hsize, _⟩ := e.subst p vm fm
    p'.ret[n] = p.ret[n] := by
  fun_induction Expr.subst <;> dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    grind
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂
      h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    grind
  next p vm fm e i p' e' fm' hsize hum hs h ih =>
    rw [hs] at ih
    grind

theorem Program.prefix_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} : p.Prefix (e.subst p vm fm).program := by
  constructor
  · exact subst_fn_eq_of_lt
  · exact subst_ty_eq_of_lt
  · exact subst_ret_eq_of_lt
  · exact (e.subst p vm fm).size_ge

grind_pattern Program.prefix_subst => (e.subst p vm fm).program

theorem Expr.types_in_subst_of_types {p : Program} {e₁ e₂ : Expr} {t : Ty}
    {vm : VarMap p.size} {fm : FunMap p.size} (ht : p ⊢ e₁ : t) :
    (e₂.subst p vm fm).program ⊢ e₁ : t :=
  (types_in_prefix_iff ht.validRefs Program.prefix_subst).mpr ht

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
  simp [mk, *] at heq

theorem update_types {p : Program} {fm : FunMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : fm.Types p) :
    (fm.update m hm).Types (p.push b p.ty[m] p.ret[m]) := by
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
    have hty : p.ty[m] = p₃.ty[p.size] := by grind [Program.subst_ty_eq_of_lt]
    have hret : p.ret[m] = p₃.ret[p.size] := by grind [Program.subst_ret_eq_of_lt]
    rw [hty, hret]
    constructor
  next p vm fm m hm m' hm' h =>
    have .fn _ _ := ht
    obtain ⟨_, hty, hret⟩ := hfm _ ‹m < p.size› m' hm'
    rw [hty, hret]
    constructor
  next => exact ht
  next => exact ht
  next =>
    cases ht with
    | app _ _ t₁ t₂ htf hte =>
      apply Types.app _ _ t₁ _ <;>
        grind [VarMap.extend_types, FunMap.subst_types]
    | pair _ _ t₁ t₂ hte₁ hte₂ =>
      constructor <;> grind [VarMap.extend_types, FunMap.subst_types]
  next =>
    have .cond _ _ _ _ htc htet htef := ht
    constructor <;>
      grind [VarMap.extend_types, FunMap.subst_types]
  next p vm fm e i p' e' fm' hsize hum hs h ih =>
    rw [hs] at ih
    cases ht with
    | proj0 _ _ t' ht =>
      constructor
      exact ih ht hvm hfm
    | proj1 _ _ t' ht =>
      constructor
      exact ih ht hvm hfm

theorem Program.subst_types {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (ht : ⊢ p) (hvm : vm.Types p) (hfm : fm.Types p) :
    ⊢ (e.subst p vm fm).program := by
  fun_induction Expr.subst <;>
    first | grind [VarMap.extend_types, FunMap.subst_types]
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have heq : p.ret[m] = (p.push (.recurse m') p.ty[m] p.ret[m]).ret[m'] := by
      simp [m']
    have ht₁ : ⊢ p₁ := by
      apply types_push ht
      conv => rhs; rw [heq]
      constructor <;> constructor
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
      · rw [prefix_subst.ret_eq (by lia), ← heq]
        exact Expr.types_in_push_of_types (ht hm)
      · exact hvm₁
      · exact hfm₁
    · rw [Vector.getElem_set_ne _ _ ‹m' ≠ i›]
      exact Expr.types_in_setBody_of_types _ (ht₂ hi)

structure FunMap.Extends {n' n : Nat} (fm' : FunMap n') (fm : FunMap n) : Prop where
  le : n ≤ n'
  eq : ∀ {m} (_ : m < n), fm[m].getD m ≠ m → fm'[m] = fm[m]
  eq_none : ∀ {m} (_ : m < n'), fm'[m] = none → ∃ (_ : m < n), fm[m] = none
  eq_of_lt : ∀ {m} (_ : m < n'), fm'[m].getD m < n →
    ∃ (_ : m < n), fm'[m] = fm[m]

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
  ∀ ⦃m r⦄ (_ : m < n), e.Local (fm[m].getD m) r → fm[m] = none

theorem Expr.noSubst_mk {n : Nat} {e : Expr} : e.NoSubst (.mk n) := by
  grind [Expr.NoSubst]

@[simp, grind =]
theorem Expr.noSubst_bin_iff {n : Nat} {k : BinKind} {e₁ e₂ : Expr} {fm : FunMap n} :
    (e₁.bin k e₂).NoSubst fm ↔ e₁.NoSubst fm ∧ e₂.NoSubst fm := by
  constructor
  · intro h
    and_intros
    · intro m r hm hl
      exact h hm (.binL _ _ _ _ hl)
    · intro m r hm hl
      exact h hm (.binR _ _ _ _ hl)
  · intro ⟨h₁, h₂⟩
    intro m r hm hl
    obtain hl | hl := local_bin_iff.mp hl
    · exact h₁ hm hl
    · exact h₂ hm hl

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

@[simp, grind =]
theorem Expr.noSubst_proj_iff {n : Nat} {e : Expr} {i : Fin 2} {fm : FunMap n} :
    (e.proj i).NoSubst fm ↔ e.NoSubst fm := by
  constructor
  · intro h m r hm hl
    exact h hm (.proj _ _ _ hl)
  · intro h m r hm hl
    have hl := local_proj_iff.mp hl
    exact h hm hl

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
    fm[m] = none → m = fm[k].getD k → m = k

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
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂
      h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    exact ih₂ (ih₁ h)
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ hf ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    exact ihef (ihet (ihc h))
  next p vm fm e i p' e' fm' hsize hum hs hf ih =>
    rw [hs] at ih
    exact ih h

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
    · grind
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
        by_cases hll'₂ : fm₂[l] = none
        · exact hll'₂
        · have hl' : fm₂[l].getD l < p.size := hvm.bounded hk hlc
          obtain ⟨hl, heq⟩ := hext.eq_of_lt hl hl'
          rw [heq] at hlc
          have := hvm.noSubst hk hkk' hne hl hlc
          grind
      · simp_all
  next => grind
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
  next => simp
  next => grind [noSubst_of_extends_of_noSubst]
  next => grind [noSubst_of_extends_of_noSubst]
  next => grind [noSubst_of_extends_of_noSubst]

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
      grind
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
      grind
    · grind [hfm.inj]
  next => grind
  next p vm fm b h => simp [FunMap.LocalProvenance]
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂
      h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    dsimp only at *
    have hvm₁ : vm.extend.Valid fm₁ := by grind
    have hfm₁ : fm₁.Valid := by grind
    obtain ⟨hv₁, hv₂⟩ := Expr.bounded_bin_iff.mp he
    obtain ⟨hns₁, hns₂⟩ := Expr.noSubst_bin_iff.mp hns
    have hf' := ih₁ hvm hfm hv₁ hns₁
    have he' := ih₂ hvm₁ hfm₁ (bounded_of_ge hsize₁ hv₂)
      (noSubst_of_extends_of_noSubst (by grind) (by grind) hns₂)
    intro n r hn hnn' hl
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hv₁' : e₁'.ValidRefs p₁ := by grind [validRefs_subst]
    obtain hl | hl := Expr.local_bin_iff.mp hl
    · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hn (hv₁' hl)
      rw [heq] at hl
      have := hf' hn (by grind) hl
      grind
    · have := he' hn hnn' hl
      grind
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
      grind [validRefs_subst, noSubst_of_extends_of_noSubst]
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
  next p vm fm e i p' e' fm' hsize hum hs hf ih =>
    rw [hs] at ih
    dsimp only at *
    intro n r hn hnn' hl
    rw [Expr.local_proj_iff] at hl ⊢
    apply ih hvm hfm <;> grind

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
  next => grind

structure Program.ValidSubst (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) where
  fn_localProvenance : ∀ {m m'} (_ : m < p.size) (_ : m' < p.size),
    m' = fm[m].getD m → m' ≠ m → fm.LocalProvenance p.fn[m] p.fn[m'] m
  fn_noSubst : ∀ {m} (_ : m < p.size), fm[m] = none → p.fn[m].NoSubst fm
  eq_of_not_nests : ∀ {m} (_ : m < p.size),
    (∀ n (_ : n < p.size), vm[n] ≠ .var n → n ⊁[p] m) → fm[m].getD m = m
  new_subst_var : ∀ {n m} (_ : n < p.size) (_ : m < p.size),
    vm[n] ≠ .var n → n ≻[p] m → fm[m].getD m = m → vm[m] = .var m
  compat : ∀ {m} (_ : m < p.size),
    fm[m].getD m ≠ m → vm[m] = .var m ∨ vm[m] = .var (fm[m].getD m)

theorem Program.validSubst_mk {p : Program} {n : Nat} {v : Expr} (hwf : p.WF) :
    p.ValidSubst (.mk _ n v) (.mk _) := by
  constructor <;> grind [Expr.NoSubst, WF]

theorem Program.validSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {l i : Nat} (hl : l < p.size) (hi : i < p.size)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvml : vm[l] ≠ .var l)
    (hnestsi : l ≻[p] i) (hvalid : p.ValidSubst vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).ValidSubst
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
      have := hvalid.fn_localProvenance hm hm' rfl hmm' hn hnn' hl
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
    · grind
    · replace hn : n < p.size := by lia
      have hin : i ≠ n := by grind
      simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, *] at hl ⊢
      exact hvalid.fn_noSubst hm heq hn hl
  case eq_of_not_nests =>
    intro m hm h
    by_cases m = p.size
    · simp [*] at *
    · replace hm : m < p.size := by lia
      by_cases i = m
      · grind
      · rw [FunMap.getElem_update_ne hi hm ‹i ≠ m›]
        apply hvalid.eq_of_not_nests
        intro n hn hne
        have := h n (by lia) (by grind)
        grind
  case new_subst_var =>
    intro n m hn hm hvmn hnests hfmm
    by_cases m = p.size
    · simp [*]
    · replace hm : m < p.size := by lia
      by_cases i = m
      · simp only [FunMap.getElem_update_eq, Option.getD_some, *] at hfmm
        lia
      · simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne,
          VarMap.getElem_update_ne, *] at hfmm ⊢
        replace hnests : n ≻[p] m := by grind
        replace hn : n < p.size := by grind
        by_cases i = n
        · subst n
          exact hvalid.new_subst_var hl hm hvml (.trans _ _ _ hnestsi hnests) hfmm
        · simp only [ne_eq, not_false_eq_true, VarMap.getElem_update_ne, *] at hvmn
          exact hvalid.new_subst_var hn hm hvmn hnests hfmm
  case compat =>
    intro m hm hmm'
    have : m ≠ p.size := by
      intro rfl
      simp at hmm'
    replace hm : m < p.size := by lia
    by_cases i = m
    · simp [*]
    · rw [FunMap.getElem_update_ne hi hm ‹_›] at hmm' ⊢
      rw [VarMap.getElem_update_ne hi hm ‹_›]
      cases hvalid.compat hm hmm' <;> simp [*]

theorem Program.validSubst_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    p'.ValidSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hvalid
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    simp only [Classical.not_forall] at h
    obtain ⟨l, hl, hf, hvml⟩ := h
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hl hm hne hf
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm heq hfm
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind [VarMap.valid_subst]
    have hfm₂ : fm₂.Valid := by grind
    have hvalid₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
      (validSubst_push_recurse hl hm hfm hp hvml hnestsm hvalid)
    have hvmm : vm[m] = .var m :=
      hvalid.new_subst_var hl hm hvml hnestsm (by simp [heq])
    have hprov : fm₂.LocalProvenance p.fn[m] f' none := by
      grind [Expr.localProvenance_subst, Expr.noSubst_of_extends_of_noSubst,
        FunMap.extends_update, hvalid.fn_noSubst]
    have hext₁ := FunMap.extends_update hm heq
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hext := FunMap.extends_trans hext₁ hext₂
    have hp₃ : p₃ = ((Expr.fn m).subst p vm fm).program := by
      grind [Expr.subst]
    have hpre : p.Prefix p₃ := hp₃ ▸ prefix_subst
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
        cases hvalid₂.fn_localProvenance hn hn' rfl hnn' hk hkk' hl <;> simp [p₃, *]
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
    case eq_of_not_nests =>
      have hnestsm₃ : l ≻[p₃] m := by
        rw [show p₃ = ((Expr.fn m).subst p vm fm).program by grind [Expr.subst]]
        exact (nests_in_prefix_iff hm hp prefix_subst).mpr hnestsm
      intro n hn h
      by_cases m = n
      · subst n
        exfalso
        exact h l (by lia) (by simpa [hl] using hvml) hnestsm₃
      · apply hvalid₂.eq_of_not_nests
        intro k hk hne hnests
        have hrec : ∀ l r, p₂.fn[m'].Local l r → l = m' := by
          intro l r hl
          rw [show p₂.fn[m'] = p₁.fn[m'] by grind] at hl
          simp [p₁, m'] at hl
          grind
        replace hnests : k ≻[p₃] n := nests_in_setBody hsize₂ hrec hnests
        grind
    case new_subst_var =>
      intro n k hn hk hvmn hnests hfmk
      have hext : fm₂.Extends fm := by grind [FunMap.extends_update]
      by_cases hk : k < p.size
      · replace hfmk : fm[k].getD k = k := by grind
        replace hnests : n ≻[p] k := by grind
        have hvmk := hvalid.new_subst_var (by grind) ‹_› (by grind) hnests hfmk
        grind
      · simp only [Nat.not_lt] at hk
        simp [*]
    case compat =>
      intro k hk hkk'
      have hext : fm₂.Extends fm := by grind [FunMap.extends_update]
      cases hvalid₂.compat hk hkk' <;> grind
  next => grind [validRefs_subst]
  next => grind [validRefs_subst]
  next => grind [validRefs_subst]

theorem Program.exists_of_ge_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : fm.Valid) {n' : Nat}
    (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    n' < p'.size → ∃ (n : Nat) (_ : n < p.size), fm'[n].getD n = n' := by
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
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂
      h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
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
  next p vm fm e i p' e' fm' hsize hum hs hf ih =>
    rw [hs] at ih
    dsimp only at *
    exact ih h hn'

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
    {n' m' k' : Nat} (hn' : p.size ≤ n') (hm' : p.size ≤ m')
    (hk' : p.size ≤ k') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    n' < p'.size → m' < p'.size → k' < p'.size → m' ⟶[p', n']* k' →
      ∃ (n m k : Nat) (hn : n < p.size) (hm : m < p.size) (hk : k < p.size),
        fm'[n].getD n = n' ∧ fm'[m].getD m = m' ∧ fm'[k].getD k = k' ∧ m ⟶[p, n]* k := by
  intro hnlt hmlt hklt hp'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hsize := (e.subst p vm fm).size_ge
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h
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
      (show l < p'.size by lia) (by lia) (by simpa [← hfml] using hlf')
    simp only [Option.some.injEq, Program.subst_fn_eq_of_lt hm, p'] at hlf
    obtain heq | hlf := hlf
    · grind
    · exact ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, .step _ _ _ hne ⟨hm, hlf⟩ hp⟩

theorem Program.free_in_fn_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    {n' m' : Nat} (hn' : p.size ≤ n') (hm' : p.size ≤ m') (hne' : n' ≠ m') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    ∀ (_ : m' < p'.size), p'.fn[m'].Free p' n' →
      ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
        fm'[n].getD n = n' ∧ fm'[m].getD m = m' ∧ p.fn[m].Free p n := by
  intro hmlt hf'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h
  obtain ⟨k', hklt, hlv', hp'⟩ := (free_in_fn_iff hmlt hne').mp hf'
  have hk' : p.size ≤ k' := by grind [subst_fn_eq_of_lt]
  have hnlt : n' < p'.size := by grind
  obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
    pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp h hn' hm' hk' hnlt hmlt hklt hp'
  have hne : n ≠ m := by grind
  have hlv := h'.fn_localProvenance
    (show k < p'.size by lia) hklt (by lia) (by grind)
    (show n < p'.size by lia) (by lia) (by simpa [← hfmn] using hlv')
  rw [subst_fn_eq_of_lt hk] at hlv
  simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
  exact ⟨n, m, hn, hm, hfmn, hfmm, (free_in_fn_iff hm hne).mpr ⟨k, hk, hlv, hp⟩⟩

theorem Expr.free_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', e', fm', _, _⟩ := e.subst p vm fm
    e'.Free p' n' → ∃ (n : Nat) (_ : n < p.size),
      fm'[n].getD n = n' ∧ e.Free p n := by
  intro hf
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := Program.validRefs_subst hvm hfm hp
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h
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
        Program.pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp h hn' hm' hk'
          ‹_› (validRefs_subst hvm hfm he hlf') ‹_› hp'
      have hlf := localProvenance_subst hvm hfm he hns
        (show m < p'.size by lia) (by lia) (by simpa [← hfmm] using hlf')
      simp only [reduceCtorEq, false_or] at hlf
      have hlv := h'.fn_localProvenance
        (show k < p'.size by lia) (show k' < p'.size by grind) (by lia) (by grind)
        (show n < p'.size by lia) (by lia) (by simpa [← hfmn] using hlv')
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

theorem Program.nests_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {m n : Nat} (hn : n < p.size)
    (hp : p.ValidRefs) (h : m ≻[(e.subst p vm fm).program] n) :
    m ≻[p] n := (nests_in_prefix_iff hn hp prefix_subst).mp h

theorem Program.nests_of_nests_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    {n' m' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    n' ≻[p'] m' → ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
      fm'[n].getD n = n' ∧ fm'[m].getD m = m' ∧ n ≻[p] m := by
  intro hnests'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h
  have hfm' : fm'.Valid := FunMap.valid_subst hfm
  induction hnests' with
  | free n' m' hltn hltm hne' hf' =>
    have hm' : p.size ≤ m' := by
      false_or_by_contra
      rename_i hm'
      simp only [Nat.not_le] at hm'
      have := lt_size_of_free_in_subst_of_lt hp hm' hne' hf'
      lia
    obtain ⟨n, m, hn, hm, hfmn, hfmm, hf⟩ :=
      Program.free_in_fn_of_free_in_subst_of_ge hvm hfm hp h hn' hm' hne' hltm hf'
    have hne : n ≠ m := by grind
    exact ⟨n, m, hn, hm, hfmn, hfmm, .free _ _ hn hm hne hf⟩
  | trans n' k' m' hnests₁' hnests₂' ih₁ ih₂ =>
    have hk' : p.size ≤ k' := by grind
    obtain ⟨n, k, hn, hk, hfmn, hfmk, hnests₁⟩ := ih₁ hn'
    obtain ⟨l, m, hl, hm, hfml, hfmm, hnests₂⟩ := ih₂ hk'
    obtain rfl : k = l :=
      hfm'.inj (by lia) (by lia) (by lia) (by lia) (by simp [fm', hfmk, hfml])
    exact ⟨n, m, hn, hm, hfmn, hfmm, .trans _ _ _ hnests₁ hnests₂⟩

theorem Program.subst_wf {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (h : p.ValidSubst vm fm) (hwf : p.WF) :
    (e.subst p vm fm).program.WF := by
  intro m hnests
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  by_cases hm : m < p.size
  · exact hwf <| nests_of_nests_in_subst_of_lt hm hp hnests
  · simp only [Nat.not_lt] at hm
    have hvalid' : p'.ValidSubst vm.extend fm' := validSubst_subst hvm hfm hp h
    have hfm' : fm'.Valid := FunMap.valid_subst hfm
    replace ⟨k, l, hk, hl, hfmk, hfml, hnests⟩ :=
      nests_of_nests_in_subst_of_ge hvm hfm hp h hm hnests
    obtain rfl : k = l :=
      hfm'.inj (by lia) (by lia) (by lia) (by lia) (by simp [fm', hfmk, hfml])
    exact hwf hnests

def Expr.WFSubst (e : Expr) (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃n m⦄ (_ : n < p.size) (_ : m < p.size),
    n ≻[p] m → e.Free p m → vm[n] ≠ var n → vm[m] ≠ var m ∧ fm[m].getD m ≠ m

@[grind =]
theorem Expr.wfSubst_bin_iff {k : BinKind} {e₁ e₂ : Expr} {p : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    (e₁.bin k e₂).WFSubst p vm fm ↔ e₁.WFSubst p vm fm ∧ e₂.WFSubst p vm fm := by
  constructor
  · intro h
    and_intros
    · intro n m hn hm hnests hf hne
      exact h hn hm hnests (.binL _ _ _ hf) hne
    · intro n m hn hm hnests hf hne
      exact h hn hm hnests (.binR _ _ _ hf) hne
  · rintro ⟨h₁, h₂⟩ n m hn hm hnests hf hne
    cases hf with
    | binL _ _ _ hf => exact h₁ hn hm hnests hf hne
    | binR _ _ _ hf => exact h₂ hn hm hnests hf hne

@[grind =]
theorem Expr.wfSubst_cond_iff {c et ef : Expr} {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} :
    (c.cond et ef).WFSubst p vm fm ↔
      c.WFSubst p vm fm ∧ et.WFSubst p vm fm ∧ ef.WFSubst p vm fm := by
  constructor
  · intro h
    and_intros
    · intro n m hn hm hnests hf hne
      exact h hn hm hnests (.condC _ _ _ hf) hne
    · intro n m hn hm hnests hf hne
      exact h hn hm hnests (.condT _ _ _ hf) hne
    · intro n m hn hm hnests hf hne
      exact h hn hm hnests (.condF _ _ _ hf) hne
  · rintro ⟨h₁, h₂, h₃⟩ n m hn hm hnests hf hne
    cases hf with
    | condC _ _ _ hf => exact h₁ hn hm hnests hf hne
    | condT _ _ _ hf => exact h₂ hn hm hnests hf hne
    | condF _ _ _ hf => exact h₃ hn hm hnests hf hne

@[grind =]
theorem Expr.wfSubst_proj_iff {e : Expr} {i : Fin 2} {p : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    (e.proj i).WFSubst p vm fm ↔ e.WFSubst p vm fm := by
  constructor
  · intro h n m hn hm hnests hf hne
    exact h hn hm hnests (.proj _ _ hf) hne
  · intro h n m hn hm hnests hf hne
    replace .proj _ _ hf := hf
    exact h hn hm hnests hf hne

theorem Expr.wfSubst_in_subst {p : Program} {e₁ e₂ : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hp : p.ValidRefs) (he : e₁.ValidRefs p)
    (h : e₁.WFSubst p vm fm) :
    let ⟨p', _, fm', _, _⟩ := e₂.subst p vm fm
    e₁.WFSubst p' vm.extend fm' := by
  grind [WFSubst]

theorem Expr.exists_free_subst_var {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n m : Nat} {r : RefKind} (he : e.ValidRefs p)
    (hwfs : e.WFSubst p vm fm) (hn : n < p.size) (hvmn : vm[n] ≠ var n)
    (hnests : n ≻[p] m) (hl : e.Local m r) :
    ∃ (k : Nat) (_ : k < p.size), vm[k] ≠ var k ∧ e.Free p k := by
  have hm := he hl
  cases r with
  | var =>
    have hf : e.Free p m := Expr.free_of_localVar hl
    obtain ⟨hvmm, -⟩ := hwfs hn hm hnests hf hvmn
    exact ⟨m, hm, hvmm, hf⟩
  | fn =>
    obtain ⟨_, k, hk, hne, hf, hnests⟩ := Program.nests_iff.mp hnests
    replace hf := free_of_localFn_of_free _ hne hl hf
    cases hnests with
    | refl _ => exact ⟨n, hn, hvmn, hf⟩
    | nests _ hnests =>
      obtain ⟨hvmk, -⟩ := hwfs hn hk hnests hf hvmn
      exact ⟨k, hk, hvmk, hf⟩

theorem FunMap.ne_in_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n m : Nat} {r : RefKind} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (he : e.ValidRefs p)
    (hwfs : e.WFSubst p vm fm) (hns : e.NoSubst fm) (hn : n < p.size)
    (hvmn : vm[n] ≠ .var n) (hl : e.Local m r) (hnests : n ≻[p] m) :
    let ⟨_, _, fm', _, _⟩ := e.subst p vm fm
    (fm'[m]'(by grind)).getD m ≠ m := by
  have hm : m < p.size := he hl
  fun_induction Expr.subst
  next p e vm fm h =>
    obtain ⟨k, hk, hvmk, hf⟩ :=
      Expr.exists_free_subst_var he hwfs hn hvmn hnests hl
    have := h k hk hf
    contradiction
  next p vm fm m h =>
    obtain ⟨rfl, rfl⟩ := Expr.local_var_iff.mp hl
    obtain ⟨-, hmm'⟩ := hwfs _ hm hnests .var hvmn
    exact hmm'
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    obtain ⟨rfl, rfl⟩ := Expr.local_fn_iff.mp hl
    have hext : fm₂.Extends fm₁ := by grind
    grind [hext.eq]
  next p vm fm m hm m' heq h =>
    obtain ⟨rfl, rfl⟩ := Expr.local_fn_iff.mp hl
    intro hfmm
    conv at hl => arg 1; rw [← hfmm]
    simp [hns _ hl] at heq
  next => grind
  next => grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    dsimp only at *
    have hext : fm₂.Extends fm₁ := by grind
    grind [Program.validRefs_subst, Expr.wfSubst_in_subst,
      Expr.noSubst_of_extends_of_noSubst]
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    grind [Program.validRefs_subst, Expr.wfSubst_in_subst,
      Expr.noSubst_of_extends_of_noSubst]
  next p vm fm e i p' e' fm' hsize hum hs hf ih =>
    rw [hs] at ih
    grind

def FunMap.StrongProvenance (p : Program) (fm : FunMap p.size)
    (vm : VarMap p.size) (e e' : Expr) (k : Option Nat) : Prop :=
  ∀ ⦃m' r⦄ (_ : m' < p.size),
    e'.Local m' r →
      ∃ (m : Nat) (_ : m < p.size),
        fm[m].getD m = m ∧ (∀ k (_ : k < p.size), vm[k] ≠ .var k → k ⊁[p] m) ∧
          (e.LocalVar m ∧ vm[m].Local m' r ∨ e.LocalFn m ∧ m' = m ∧ r = .fn) ∨
          fm[m].getD m = m' ∧ (m = k ∨ e.Local m r ∧ m' ≠ m)

theorem FunMap.strongProvenance_bin {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {k : BinKind} {e₁ e₁' e₂ e₂' : Expr}
    (hf : fm.StrongProvenance p vm e₁ e₁' none)
    (he : fm.StrongProvenance p vm e₂ e₂' none) :
    fm.StrongProvenance p vm (e₁.bin k e₂) (e₁'.bin k e₂') none := by
  intro n r hn hl
  cases hl with grind [StrongProvenance, intro Expr.Local]

theorem FunMap.strongProvenance_cond {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {c c' et et' ef ef' : Expr}
    (hc : fm.StrongProvenance p vm c c' none)
    (het : fm.StrongProvenance p vm et et' none)
    (hef : fm.StrongProvenance p vm ef ef' none) :
    fm.StrongProvenance p vm (c.cond et ef) (c'.cond et' ef') none := by
  intro n r hn hl
  cases hl with grind [StrongProvenance, intro Expr.Local]

theorem FunMap.strongProvenance_proj {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {e e' : Expr} {i : Fin 2}
    (he : fm.StrongProvenance p vm e e' none) :
    fm.StrongProvenance p vm (e.proj i) (e'.proj i) none := by
  intro n r hn hl
  cases hl with grind [StrongProvenance, intro Expr.Local]

theorem Expr.strongProvenance_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (hwf : p.WF) (he : e.ValidRefs p)
    (hns : e.NoSubst fm) (hwfe : e.WFSubst p vm fm) :
    let ⟨p', e', fm', _, _⟩ := e.subst p vm fm
    fm'.StrongProvenance p' vm.extend e e' none := by
  fun_induction subst
  next p e vm fm h =>
    intro n r hn hl
    have hnnests : ∀ m (_ : m < p.size), vm[m] ≠ var m → m ⊁[p] n := by
      intro m hm hvmm hnests
      obtain ⟨k, hk, hvmk, hf⟩ :=
        exists_free_subst_var he hwfe hm hvmm hnests hl
      have := h k hk hf
      contradiction
    have hfmn := hvalid.eq_of_not_nests hn hnnests
    refine ⟨n, hn, Or.inl ⟨hfmn, by grind, ?_⟩⟩
    cases r with
    | var =>
      have hf := h _ hn (free_of_localVar hl)
      exact Or.inl ⟨hl, by simp [*]⟩
    | fn => exact Or.inr ⟨hl, rfl, rfl⟩
  next p vm fm m h =>
    intro n r hn hl
    by_cases hm : m < p.size
    · simp only [Classical.not_forall] at h
      obtain ⟨k, hk, hf, hvmk⟩ := h
      have .var := hf
      simp only [getElem?_pos, Option.getD_some, hk] at hl
      by_cases hkk' : fm[k].getD k = k
      · refine ⟨k, hk, Or.inl ⟨hkk', ?_, Or.inl ⟨.var, by grind⟩⟩⟩
        intro l hl hvml hnests
        exact hvmk <| hvalid.new_subst_var hl hk (by grind) hnests hkk'
      · refine ⟨k, hk, Or.inr ?_⟩
        cases hvalid.compat hk hkk' <;> grind
    · simp_all
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    intro m'' r hm' hl
    simp only [Expr.local_fn_iff, f''] at hl
    obtain ⟨hr, rfl⟩ := hl
    have hext : fm₂.Extends fm₁ := by grind
    exact ⟨m, by lia, Or.inr (by grind [hext.eq])⟩
  next p vm fm m hm m' heq h =>
    intro n r hn hl
    simp only [local_fn_iff] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨m, hm, Or.inr ⟨by simp [heq], Or.inr ⟨.fn, ?_⟩⟩⟩
    by_cases m' = m
    · have hl : (fn m).Local (fm[m].getD m) .fn := by simp [*]
      simp [hns _ hl] at heq
    · simp [*]
  next p vm fm m hm h =>
    intro m' r hm' hl
    simp only [local_fn_iff] at hl
    lia
  next p vm fm c h =>
    intro m' r hm' hl
    simp at hl
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ hsize₁ hum₁ hs₁ p₂ e₂' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    dsimp only at *
    have hp₁ : p₁.ValidRefs := by grind [Program.validRefs_subst]
    have hvalid₂ : p₂.ValidSubst vm.extend fm₂ := by
      grind [Program.validSubst_subst]
    have he₁' : fm₁.StrongProvenance p₁ vm.extend e₁ e₁' none := by grind
    have he₂' : fm₂.StrongProvenance p₂ vm.extend e₂ e₂' none := by
      grind [noSubst_of_extends_of_noSubst, wfSubst_in_subst,
        Program.validSubst_subst, Program.subst_wf]
    have hext : fm₂.Extends fm₁ := by grind
    replace he₁' : fm₂.StrongProvenance p₂ vm.extend e₁ e₁' none := by
      intro n r hn hl
      replace hn : n < p₁.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := he₁' hn hl
      · refine ⟨m, by lia, Or.inl
          ⟨hvalid₂.eq_of_not_nests (by lia) ?hf, ?hf, by grind⟩⟩
        grind
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    exact FunMap.strongProvenance_bin he₁' he₂'
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    have hp₁ : p₁.ValidRefs := by grind [Program.validRefs_subst]
    have hp₂ : p₂.ValidRefs := by grind [Program.validRefs_subst]
    have hvalid₃ : p₃.ValidSubst vm.extend fm₃ := by
      grind [Program.validRefs_subst, Program.validSubst_subst]
    have hc' : fm₁.StrongProvenance p₁ vm.extend c c' none := by grind
    have het' : fm₂.StrongProvenance p₂ vm.extend et et' none := by
      grind [noSubst_of_extends_of_noSubst, wfSubst_in_subst,
        Program.validRefs_subst, Program.validSubst_subst, Program.subst_wf]
    have hef' : fm₃.StrongProvenance p₃ vm.extend ef ef' none := by
      grind [noSubst_of_extends_of_noSubst, wfSubst_in_subst,
        Program.validRefs_subst, Program.validSubst_subst, Program.subst_wf]
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    replace hc' : fm₃.StrongProvenance p₃ vm.extend c c' none := by
      intro n r hn hl
      replace hn : n < p₁.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := hc' hn hl
      · refine ⟨m, by lia, Or.inl
          ⟨hvalid₃.eq_of_not_nests (by lia) ?hc, ?hc, by grind⟩⟩
        grind
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    replace het' : fm₃.StrongProvenance p₃ vm.extend et et' none := by
      intro n r hn hl
      replace hn : n < p₂.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := het' hn hl
      · refine ⟨m, by lia, Or.inl
          ⟨hvalid₃.eq_of_not_nests (by lia) ?het, ?het, by grind⟩⟩
        grind
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    exact FunMap.strongProvenance_cond hc' het' hef'
  next p vm fm e i p' e' fm' hsize hum hs hf ih =>
    rw [hs] at ih
    apply FunMap.strongProvenance_proj
    grind

theorem Program.push_wf {p : Program} {b : Expr} {t₁ t₂ : Ty} (hp : p.ValidRefs)
    (h : p.WF) : (p.push b t₁ t₂).WF := by
  intro n hnests
  have hn := lt_size_right_of_nests hnests
  by_cases n = p.size
  · obtain ⟨_, m, hm, hne, hf, hnests⟩ := nests_iff.mp hnests
    cases hnests with
    | refl _ => contradiction
    | nests _ hnests => grind
  · replace hn : n < p.size := by lia
    grind [WF]

def Program.WFSubst (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) :
    Prop :=
  ∀ ⦃m m'⦄ (_ : m < p.size) (_ : m' < p.size),
    fm[m].getD m = m' → m' ≠ m → fm.StrongProvenance p vm p.fn[m] p.fn[m'] m

theorem Program.wfSubst_fn_mk {p : Program} {n : Nat} {v : Expr}
    (hn : n < p.size) (hwf : p.WF) :
    p.fn[n].WFSubst p (.mk _ n v) (.mk _) := by
  intro k m hk hm hnests hf hne
  by_cases n = k
  · subst k
    simp only [VarMap.mk, Vector.getElem_setIfInBounds_self, ne_eq] at hne
    exfalso
    by_cases h : m = n
    · subst m
      exact hwf hnests
    · exact hwf (nests_iff.mpr ⟨hk, _, hm, h, hf, .nests _ hnests⟩)
  · simp [VarMap.mk, *] at hne

theorem Program.wfSubst_mk {p : Program} {n : Nat} {v : Expr} :
    p.WFSubst (.mk _ n v) (.mk _) := by
  grind [WF, WFSubst]

theorem Program.wfSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} (hfm : fm.Valid) (hp : p.ValidRefs) {l i : Nat}
    (hl : l < p.size) (hi : i < p.size) (hvml : vm[l] ≠ .var l)
    (hfmi : fm[i] = none) (hnestsi : l ≻[p] i) (hwfs : p.WFSubst vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).WFSubst
      (vm.update i hi) (fm.update i hi) := by
  intro m m' hm hm' rfl hmm'
  by_cases m = p.size
  · simp [*] at hmm'
  · replace hm : m < p.size := by lia
    by_cases i = m
    · intro n r hn hlc
      grind
    · intro n r hn hlc
      replace hm' : fm[m].getD m < p.size := by grind
      simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne,
        Vector.getElem_push_lt, *] at hlc hmm'
      replace hn : n < p.size := by grind
      obtain ⟨k, hk, ⟨hvmk, hnnests, hlc⟩ | ⟨hfmk, heq | ⟨hlc, h⟩⟩⟩ :=
        hwfs hm hm' rfl hmm' hn hlc
      · have : i ≠ k := by grind
        exact ⟨k, by lia, Or.inl ⟨by simp [*], by grind, by simp [*]⟩⟩
      · grind
      · have : i ≠ k := by grind
        exact ⟨k, by lia, by simp [*]⟩

theorem Program.wfSubst_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm) (hwf : p.WF)
    (hwfs : p.WFSubst vm fm) (he : e.ValidRefs p)
    (hwfe : e.WFSubst p vm fm) :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    p'.WFSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hwfs
  next p vm fm m hm heq m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at *
    simp only [Classical.not_forall] at h
    obtain ⟨l, hl, hf, hvml⟩ := h
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hl hm hne hf
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm heq hfm
    have hp₁ : p₁.ValidRefs := validRefs_push hp (by grind)
    have hvalid₁ : p₁.ValidSubst vm₁ fm₁ :=
      validSubst_push_recurse hl hm hfm hp hvml hnestsm hvalid
    have hwf₁ : p₁.WF := push_wf hp hwf
    have hwfs₁ : p₁.WFSubst vm₁ fm₁ :=
      wfSubst_push_recurse hfm hp hl hm hvml heq hnestsm hwfs
    have hfnm : p.fn[m].ValidRefs p₁ := Expr.validRefs_in_push (hp hm)
    have hwfsm : p.fn[m].WFSubst p₁ vm₁ fm₁ := by
      intro n k hn hk hnests hf hne
      by_cases m = k
      · grind
      · replace hn : n < p.size := by grind
        simp only [ne_eq, vm₁] at hne ⊢
        replace hnests : n ≻[p] k := by grind
        replace hf : p.fn[m].Free p k := by grind
        replace hk : k < p.size :=
          Expr.lt_size_of_free hp (hp hm) hf
        rw [VarMap.getElem_update_ne hm hk ‹_›]
        have hmn : m ≠ n := by
          intro rfl
          exfalso
          exact hwf (nests_iff.mpr ⟨hm, _, hk, ‹m ≠ k›.symm, hf, .nests _ hnests⟩)
        have := hwfe hn hk hnests (.fn _ hm ‹m ≠ k›.symm hf)
        grind
    have hwfs₂ := ih hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ hwfs₁ hfnm hwfsm
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := by grind
    have hfmm : fm₂[m].getD m = m' := by grind [hext₁.eq]
    have hfmm' : fm₂[m'].getD m' = m' := by grind
    have hp₃ : p₃ = ((Expr.fn m).subst p vm fm).program := by
      grind [Expr.subst]
    have hpre : p.Prefix p₃ := hp₃ ▸ prefix_subst
    intro n n' hn hn' rfl hnn'
    replace hn : n < p.size := by
      false_or_by_contra
      have hn' : p₁.size ≤ n := by grind
      obtain ⟨k, hk, hfmk⟩ :=
        exists_of_ge_in_subst (e := p.fn[m]) (vm := vm₁) hfm₁ hn' (by lia)
      have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
      subst p₂
      grind
    by_cases m = n
    · subst n
      simp only [ne_eq, show m' ≠ m by lia, not_false_eq_true, Vector.getElem_set_ne,
        Vector.getElem_set_self, p₃, hfmm]
      have hf' := Expr.strongProvenance_subst hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ hfnm
        (Expr.noSubst_of_extends_of_noSubst (by grind) (FunMap.extends_update hm heq)
          (hvalid.fn_noSubst hm heq)) hwfsm
      rw [hs₂] at hf'
      dsimp only at hf'
      rw [show p₂.fn[m] = p.fn[m] by grind]
      intro k r hk hlc
      obtain ⟨l, hl, ⟨hll', hnnests, h⟩ | ⟨hfml, h | ⟨hlc, h⟩⟩⟩ := hf' hk hlc
      · by_cases m = l
        · exact ⟨m, by lia, Or.inr (by grind)⟩
        · exact ⟨l, hl, Or.inl ⟨hll', by grind, by grind⟩⟩
      · contradiction
      · exact ⟨l, hl, Or.inr ⟨hfml, Or.inr ⟨hlc, h⟩⟩⟩
    · have : m' ≠ n := by grind
      have : m' ≠ fm₂[n].getD n := by
        intro h
        have := hfm₂.inj (show m < p₂.size by lia) (by lia) (by lia) hnn' (hfmm ▸ h)
        contradiction
      simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, p₃, *]
      intro k r hk hlc
      obtain ⟨l, hl, ⟨hmm', hnnests, h⟩ | ⟨hfml, h | ⟨hlc, h⟩⟩⟩ :=
        hwfs₂ (by lia) (by lia) rfl hnn' hk hlc
      · by_cases m = l
        · exact ⟨m, by lia, Or.inr (by grind)⟩
        · rw [show vm₁.extend[l] = vm.extend[l] by grind] at h
          refine ⟨l, hl, Or.inl ⟨hmm', ?_, h⟩⟩
          rw [show p₂.fn[n] = p.fn[n] by grind] at h
          replace hl : l < p.size := by grind
          intro o ho hvmo hnests
          replace hnests : o ≻[p₂] l := by grind
          exact hnnests o ho (by grind) hnests
      · grind
      · grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    grind [validRefs_subst, validSubst_subst, subst_wf, Expr.wfSubst_in_subst]
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    grind [validRefs_subst, validSubst_subst, subst_wf, Expr.wfSubst_in_subst]
  next => grind

theorem Program.free_in_fn_of_free_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (hwf : p.WF) (hwfs : p.WFSubst vm fm) (he : e.ValidRefs p)
    (hwfe : e.WFSubst p vm fm) {n' m m' : Nat} (hm : m < p.size) :
    let ⟨p', _, fm', _, _⟩ := e.subst p vm fm
    ∀ (_ : m' < p'.size), fm'[m].getD m = m' → m' ≠ m → n' ≠ m' → p'.fn[m'].Free p' n' →
      ∃ (n : Nat) (hn : n < p.size), p.fn[m].Free p n ∧
          (fm'[n].getD n = n ∧ vm[n].Free p n' ∨ fm'[n].getD n = n' ∧ n' ≠ n) := by
  intro hm' hfmm hmm' hne hf
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  let hsize := (e.subst p vm fm).size_ge
  have hfm' : fm'.Valid := FunMap.valid_subst hfm
  have hp' : p'.ValidRefs := validRefs_subst hvm hfm hp
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    validSubst_subst hvm hfm hp hvalid
  have hwfs' : p'.WFSubst vm.extend fm' :=
    wfSubst_subst hvm hfm hp hvalid hwf hwfs he hwfe
  obtain ⟨k', hk', hlv, hpath⟩ := (free_in_fn_iff _ hne).mp hf
  induction hpath generalizing m with
  | refl m' hne =>
    have hn' : n' < p'.size := by grind
    obtain ⟨n, hn, ⟨hnn', hvmn, ⟨hlv, hlc⟩ | h⟩ | ⟨hfmn, h | ⟨hlc, hnn'⟩⟩⟩ :=
      hwfs' (by lia) hm' hfmm hmm' hn' hlv
    · rw [subst_fn_eq_of_lt hm] at hlv
      replace hn : n < p.size := hp hm hlv
      simp only [hn, VarMap.getElem_extend_lt] at hlc
      exact ⟨n, hn, Expr.free_of_localVar hlv,
        Or.inl ⟨hnn', Expr.free_of_localVar hlc⟩⟩
    · grind
    · grind
    · rw [subst_fn_eq_of_lt hm] at hlc
      replace hn : n < p.size := hp hm hlc
      exact ⟨n, hn, Expr.free_of_localVar hlc, Or.inr ⟨hfmn, hnn'⟩⟩
  | step m' l' k' hne hs hpath ih =>
    have hmm' : m' ≠ m := by lia
    obtain ⟨_, hlf⟩ := hs
    have hl' : l' < p'.size := by grind
    obtain ⟨l, hl, ⟨hll', hnnests, ⟨hlvm, hlf⟩ | ⟨hlf, rfl, -⟩⟩ | ⟨hfml, h | ⟨hlf, hll'⟩⟩⟩ :=
      hwfs' (by lia) hm' hfmm hmm' hl' hlf
    · replace hl : l < p.size := by grind
      replace hlf : vm[l].LocalFn l' := by grind
      replace hl' : l' < p.size := by grind
      replace hk' : k' < p.size := lt_size_of_pathWithout_of_lt hp hl' hpath
      replace hpath : l' ⟶[p, n']* k' := by grind
      rw [subst_fn_eq_of_lt hm] at hlvm
      rw [subst_fn_eq_of_lt hk'] at hlv
      exact ⟨l, hl, Expr.free_of_localVar hlvm,
        Or.inl ⟨hll', Expr.free_iff.mpr (Or.inr ⟨l', k', hk', hlf, hpath, hlv⟩)⟩⟩
    · replace hl' : l' < p.size := by grind
      replace hk' : k' < p.size := lt_size_of_pathWithout_of_lt hp hl' hpath
      have hn' : n' < p.size := by grind
      have hne := hpath.ne_start
      have hnn' : fm'[n'].getD n' = n' := by
        apply hvalid'.eq_of_not_nests
        intro n hn hvmn hnests
        refine hnnests n hn hvmn
          (.trans _ _ _ hnests (.free _ _ (by lia) (by lia) hne ?_))
        exact (free_in_fn_iff (by lia) hne).mpr ⟨_, ‹_›, hlv, hpath⟩
      replace hpath : l' ⟶[p, n']* k' := by grind
      rw [subst_fn_eq_of_lt hm] at hlf
      rw [subst_fn_eq_of_lt hk'] at hlv
      have hne := hpath.ne_start
      replace hf : p.fn[l'].Free p n' :=
        (free_in_fn_iff hl' hne).mpr ⟨_, hk', hlv, hpath⟩
      have hvmn' : vm[n'] = .var n' := by
        false_or_by_contra
        rename_i hvmn'
        grind [Nests.free]
      exact ⟨n', hn', free_in_fn_of_succ hm hl' hne ⟨hm, hlf⟩ hf,
        Or.inl ⟨hnn', hvmn' ▸ .var⟩⟩
    · grind
    · rw [subst_fn_eq_of_lt hm] at hlf
      replace hl : l < p.size := by grind
      replace hne := hpath.ne_start
      replace hf := (free_in_fn_iff hl' hne).mpr ⟨k', hk', hlv, hpath⟩
      obtain ⟨n, hn, hf, h⟩ := ih hl hl' hfml hll' hne hf hk' hlv
      exact ⟨n, hn, free_in_fn_of_succ hm hl (by grind) ⟨hm, hlf⟩ hf, h⟩

theorem Expr.free_of_free_in_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (hwf : p.WF) (hwfs : p.WFSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) (hwfe : e.WFSubst p vm fm)
    {n' : Nat} :
    let ⟨p', e', fm', _, _⟩ := e.subst p vm fm
    e'.Free p' n' → ∃ (n : Nat) (hn : n < p.size), e.Free p n ∧
      (fm'[n].getD n = n ∧ vm[n].Free p n' ∨ fm'[n].getD n = n' ∧ n' ≠ n) := by
  intro hf
  let p' := (e.subst p vm fm).program
  let e' := (e.subst p vm fm).expr
  let fm' := (e.subst p vm fm).funMap
  let hsize := (e.subst p vm fm).size_ge
  have hfm' : fm'.Valid := FunMap.valid_subst hfm
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid
  have he' : e'.ValidRefs p' := validRefs_subst hvm hfm he
  obtain hlv | ⟨m', k', hk', hlf, hpath, hlv⟩ := free_iff.mp hf
  · have hn' : n' < p'.size := by grind
    obtain ⟨n, hn, ⟨hnn', hnnests, ⟨hlv, hl⟩ | ⟨-, -, h⟩⟩ | ⟨hfmn, h | ⟨hlv, hnn'⟩⟩⟩ :=
      strongProvenance_subst hvm hfm hp hvalid hwf he hns hwfe hn' hlv
    · exact ⟨n, he hlv, free_of_localVar hlv,
        Or.inl ⟨hnn', free_of_localVar (by grind)⟩⟩
    · contradiction
    · contradiction
    · exact ⟨n, he hlv, free_of_localVar hlv, Or.inr ⟨hfmn, hnn'⟩⟩
  · have hm' : m' < p'.size := by grind
    have hne := hpath.ne_start
    replace hf' := (Program.free_in_fn_iff hm' hne).mpr ⟨_, hk', hlv, hpath⟩
    obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hlf, hmm'⟩⟩⟩ :=
      strongProvenance_subst hvm hfm hp hvalid hwf he hns hwfe hm' hlf
    · replace hm : m < p.size := by grind
      replace hm' : m' < p.size := by grind
      obtain ⟨hlv, hlc⟩ | ⟨hlf, rfl, -⟩ := h
      · refine ⟨m, hm, free_of_localVar hlv, Or.inl ⟨hmm', ?_⟩⟩
        exact free_of_localFn_of_free hm' hne (by grind) (by grind)
      · have hn' : n' < p.size := by grind
        have hnn' : fm'[n'].getD n' = n' := by
          apply hvalid'.eq_of_not_nests
          intro n hn hvmn hnests
          refine hnnests n hn hvmn
            (.trans _ _ _ hnests (.free _ _ (by lia) (by lia) hne ?_))
          exact (Program.free_in_fn_iff (by lia) hne).mpr ⟨_, ‹_›, hlv, hpath⟩
        have hvmn' : vm[n'] = .var n' := by
          false_or_by_contra
          rename_i hvmn'
          exact hnnests n' (by lia) (by grind) (.free _ _ (by lia) (by lia) hne hf')
        exact ⟨n', hn', free_of_localFn_of_free hm' hne hlf (by grind),
          Or.inl ⟨hnn', hvmn' ▸ Free.var⟩⟩
    · contradiction
    · replace hm : m < p.size := by grind
      obtain ⟨n, hn, hf, h⟩ :=
        Program.free_in_fn_of_free_in_subst hvm hfm hp hvalid hwf hwfs he hwfe
        hm hm' hfmm hmm' hne hf'
      exact ⟨n, hn, free_of_localFn_of_free hm (by grind) hlf hf, h⟩

theorem Computation.free_of_free_in_subst {c : Computation} {n m : Nat}
    {v : Expr} (hp : c.ValidRefs) (he : c.expr.ValidRefs c.toProgram)
    (hv : v.ValidRefs c.toProgram) (hwf : c.WF)
    (hwfe : ∀ k, c.expr.Free c.toProgram k → k ≽[c.toProgram] n)
    (hf : (c.subst n v).Free m) : c.Free m ∧ m ≠ n ∨ v.Free c.toProgram m := by
  obtain ⟨p, e⟩ := c
  dsimp only at *
  let vm := VarMap.mk p.size n v
  let fm := FunMap.mk p.size
  let hvm : vm.Valid fm := VarMap.valid_mk hv
  let hfm : fm.Valid := FunMap.valid_mk
  let hvalid : p.ValidSubst vm fm := Program.validSubst_mk hwf
  have hnnests : ∀ k, e.Free p k → n ⊁[p] k := by
    intro k hf hnests
    cases hwfe _ hf with
    | refl _ => exact hwf hnests
    | nests _ h => exact hwf (.trans _ _ _ hnests h)
  have hwfs : e.WFSubst p vm fm := by
    intro k l hk hl hnests hf h
    have : n ≠ k := by
      intro rfl
      exact hnnests _ hf hnests
    simp [VarMap.mk, vm, *] at h
  let p' := (e.subst p (VarMap.mk _ n v) (FunMap.mk _)).program
  let fm' := (e.subst p (VarMap.mk _ n v) (FunMap.mk _)).funMap
  let hsize := (e.subst p (VarMap.mk _ n v) (FunMap.mk _)).size_ge
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid
  obtain ⟨k, hk, hf, ⟨hkk', hf'⟩ | ⟨hfmk, hne⟩⟩ :=
    Expr.free_of_free_in_subst hvm hfm hp hvalid hwf Program.wfSubst_mk he
    Expr.noSubst_mk hwfs hf
  · by_cases n = k
    · subst k
      simp only [VarMap.mk, Vector.getElem_setIfInBounds_self, vm] at hf'
      exact Or.inr hf'
    · simp [VarMap.mk, vm, *] at hf'
      have .var := hf'
      exact Or.inl ⟨hf, ‹n ≠ m›.symm⟩
  · have hkk' : fm'[k].getD k = k := by
      apply hvalid'.eq_of_not_nests
      intro l hl hvml hnests
      obtain rfl : n = l := by grind
      replace hnests : n ≻[p] k := by grind
      exact hnnests _ hf hnests
    rw [hfmk] at hkk'
    contradiction

/--
Substitution preserves types.

This proves the typing conclusions of Lemma 3 from the paper, the rest is
`Computation.subst_wf`.
-/
theorem Computation.subst_types {c : Computation} {t : Ty} {n : Nat} {v : Expr}
    (hn : n < c.size) (ht : ⊢ c : t) (hv : c.toProgram ⊢ v : c.ty[n]) :
    ⊢ c.subst n v : t := by
  refine ⟨Program.subst_types ht.program_types ?hvm ?hfm,
          Expr.subst_types ht.expr_types ?hvm ?hfm⟩
  · exact VarMap.mk_types hn hv
  · exact FunMap.mk_types

/--
Substitution preserves well-formedness.

This proves the well-formedness conclusion of Lemma 3 from the paper, the rest
is `Computation.subst_types`.
-/
theorem Computation.subst_wf {c : Computation} {n : Nat} {v : Expr}
    (hp : c.ValidRefs) (hv : v.ValidRefs c.toProgram) (h : c.WF) :
    (c.subst n v).WF :=
  Program.subst_wf (VarMap.valid_mk hv) FunMap.valid_mk hp
    (Program.validSubst_mk h) h
