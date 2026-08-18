module

import all LambdaGraph.SubstMaps
public import LambdaGraph.Nest

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

@[grind]
structure SubstProps (p p' : Program) (e e' : Expr) (vm : VarMap p.size)
    (fm : FunMap p.size) (fm' : FunMap p'.size) : Prop where
  pre : p.Prefix p'
  op : Termination.OccursProvenance p p' vm vm.extend fm fm'
  ep : Termination.ExprProvenance p p' e e' vm fm
  ext : ∀ (m : Nat) hm, fm[m]'hm ≠ m → fm'[m] = fm[m]

/--
The result of a substitution.

This contains the updated program and expression, the new function map, as well
as some evidence used in the termination proof.
-/
structure SubstResult (p : Program) (e : Expr) (vm : VarMap p.size) (fm : FunMap p.size) : Type where
  program : Program
  expr : Expr
  funMap : FunMap program.size
  props : SubstProps p program e expr vm fm funMap

open Classical Termination in
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
    (fm : FunMap p.size) : SubstResult p e vm fm :=
  if ∀ n, e.Free p n → ¬vm.Dom n then
    -- The expression does not contain a free substitution variable, so there is
    -- nothing to do.
    ⟨p, e, fm, by rfl, by simp, by simp, by simp⟩
  else
    match e with
    | var m =>
      ⟨p, vm[m]?.getD (var m), fm, by rfl, by simp, by grind, by simp⟩
    | fn m =>
      if hm : m < p.size then
        if hfmm : fm.Dom m then
          -- There is already a substitution for this function, we can reuse it.
          ⟨p, fn fm[m], fm, by rfl, by simp, by grind, by simp⟩
        else
          -- There is not yet a substitution for this function, so we have to
          -- create a new one.
          let m' := p.size
          let vm₁ := vm.update m
          let fm₁ := fm.update m
          -- Add a new function with a temporary body that is always well-typed.
          let p₁ := p.push (recurse m') p.ty[m] p.ret[m]
          -- Substitute the body to obtain the body for the new function.
          let ⟨p₂, f', fm₂, h⟩ := p.fn[m].subst p₁ vm₁ fm₁
          -- Now put the final function body in place.
          let p₃ := p₂.setBody m' f'
          let e' := fn m'
          ⟨p₃, e', fm₂, by
            refine ⟨?_, ?_, ?_, ?_⟩
            · constructor <;> grind
            · have hop' : OccursProvenance p p₂ vm vm₁.extend fm fm₂ := by
                grind [Occurs, OccursProvenance, Program.UsesFn]
              grind [Occurs, OccursProvenance, Program.UsesFn]
            · grind [ExprProvenance]
            · grind [FunMap.Dom]
          ⟩
      else
        -- This case is actually impossible, nonexistent functions don't have
        -- free variables.
        ⟨p, fn m, fm, by rfl, by simp, by simp, by simp⟩
    | const c =>
      -- This case is actually impossible, constants don't have free variables.
      ⟨p, const c, fm, by rfl, by simp, by simp, by simp⟩
    | bin k e₁ e₂ =>
      let ⟨p₁, e₁', fm₁, h₁⟩ := e₁.subst p vm fm
      let ⟨p₂, e₂', fm₂, h₂⟩ := e₂.subst p₁ vm.extend fm₁
      ⟨p₂, e₁'.bin k e₂', fm₂, by constructor <;> grind⟩
    | cond c et ef =>
      let ⟨p₁, c', fm₁, h₁⟩ := c.subst p vm fm
      let vm₁ := vm.extend
      let ⟨p₂, et', fm₂, h₂⟩ := et.subst p₁ vm₁ fm₁
      let ⟨p₃, ef', fm₃, h₃⟩ := ef.subst p₂ vm₁.extend fm₂
      ⟨p₃, c'.cond et' ef', fm₃, by constructor <;> grind⟩
    | proj e i =>
      let ⟨p', e', fm', h⟩ := e.subst p vm fm
      ⟨p', e'.proj i, fm', by constructor <;> grind⟩
      termination_by (invalidFns p e vm fm |>.size, reachableUnmapped p e fm |>.size, e)
decreasing_by
  · have hop : OccursProvenance p p₁ vm vm₁ fm fm₁ :=
      occursProvenance_push hm (by grind)
    have hi : invalidFns p₁ p.fn[m] vm₁ fm₁ ⊆ invalidFns p₁ (fn m) vm₁ fm₁ := by
      intro n h
      grind [intro Occurs, Program.UsesFn]
    have hr : reachableUnmapped p₁ p.fn[m] fm₁ ⊆ reachableUnmapped p₁ (fn m) fm₁ := by
      intro n h
      grind [Reachable.there]
    have hm₁ : m ∉ reachableUnmapped p₁ (fn m) fm₁ := by grind
    have hm₂ : m ∈ reachableUnmapped p (fn m) fm := by grind [FunMap.Dom]
    grind
  all_goals grind

/-- Substitutes a value for a variable in a computation. -/
public noncomputable def Computation.subst (p : Computation) (n : Nat) (v : Expr) :
    Computation :=
  let ⟨p', e', _, _⟩ := p.expr.subst p.toProgram (.mk _ n v) (.mk _)
  ⟨p', e'⟩

theorem Program.prefix_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} : p.Prefix (e.subst p vm fm).program :=
  (e.subst p vm fm).props.pre

grind_pattern Program.prefix_subst => (e.subst p vm fm).program

public theorem Computation.prefix_subst {c : Computation} {n : Nat} {v : Expr} :
    c.Prefix (c.subst n v).toProgram := Program.prefix_subst

grind_pattern Computation.prefix_subst => c.subst n v

theorem FunMap.subst_types {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hfm : fm.Types p) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    fm'.Types p' := by
  dsimp only
  fun_induction Expr.subst <;> try grind
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih
    exact ih <| update_types hm hfm

theorem Expr.subst_types {p : Program} {e : Expr} {t : Ty} {vm : VarMap p.size}
    {fm : FunMap p.size} (ht : p ⊢ e : t) (hvm : vm.Types p) (hfm : fm.Types p) :
    let ⟨p', e', _, _⟩ := e.subst p vm fm
    p' ⊢ e' : t := by
  fun_induction subst generalizing t <;> dsimp only at *
  next => exact ht
  next p vm fm m h =>
    by_cases hm : m < p.size
    · simp only [hm, getElem?_pos, Option.getD_some]
      have .var _ _ := ht
      apply hvm
    · simp [hm, ht]
  next p vm fm m hm hfmm hf =>
    have .fn _ _ := ht
    obtain ⟨_, hty, hret⟩ := hfm _ ‹m < p.size›
    rw [hty, hret]
    constructor
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have .fn _ _ := ht
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst hp₂
    have hty : p.ty[m] = p₃.ty[p.size] := by grind [Program.prefix_subst.ty_eq]
    have hret : p.ret[m] = p₃.ret[p.size] := by grind [Program.prefix_subst.ret_eq]
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
  next p vm fm e i p' e' fm' h hs hf ih =>
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
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' hf ih =>
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
      rw [Vector.getElem_set_self hi]
      apply Expr.subst_types
      · rw [prefix_subst.ret_eq (by lia), ← heq]
        exact Expr.types_in_push_of_types (ht hm)
      · exact hvm₁
      · exact hfm₁
    · rw [Vector.getElem_set_ne _ _ ‹m' ≠ i›]
      exact Expr.types_in_setBody_of_types _ (ht₂ hi)

def FunMap.Original {n : Nat} (fm : FunMap n) (m : Nat) : Prop :=
  m < n ∧ ∀ ⦃k⦄ (_ : k < n), fm[k] = m → m = k

@[grind →]
theorem FunMap.Original.lt {n : Nat} {fm : FunMap n} {m : Nat}
    (h : fm.Original m) : m < n := h.1

@[grind →]
theorem FunMap.Original.map {n : Nat} {fm : FunMap n} {m : Nat}
    (hm : m < n) (h : fm.Original fm[m]) : ¬fm.Dom m := by
  rintro ⟨_, hne⟩
  have := h.2 hm rfl
  contradiction

theorem FunMap.original_update {n : Nat} {fm : FunMap n} {m k : Nat}
    (hm : m < n) (h : fm.Original k) : (fm.update m hm).Original k := by
  grind [Original]

def Expr.Original (e : Expr) {n : Nat} (fm : FunMap n) : Prop :=
  ∀ ⦃m r⦄, e.Local m r → fm.Original m

@[grind →]
theorem Expr.Original.bounded {e : Expr} {n : Nat} {fm : FunMap n}
    (h : e.Original fm) : e.Bounded n :=
  fun _ _ hl => (h hl).1

@[simp, grind =]
theorem Expr.original_var_iff {n m : Nat} {fm : FunMap n} :
    (var m).Original fm ↔ fm.Original m := by
  constructor
  · intro h
    exact h .var
  · intro h k r hl
    grind

@[simp, grind =]
theorem Expr.original_fn_iff {n m : Nat} {fm : FunMap n} :
    (fn m).Original fm ↔ fm.Original m := by
  constructor
  · intro h
    exact h .fn
  · intro h k r hl
    grind

@[simp, grind .]
theorem Expr.original_const {n : Nat} {c : Const} {fm : FunMap n} :
    (const c).Original fm := nofun

@[simp, grind =]
theorem Expr.original_bin_iff {n : Nat} {k : BinKind} {e₁ e₂ : Expr}
    {fm : FunMap n} :
    (e₁.bin k e₂).Original fm ↔ e₁.Original fm ∧ e₂.Original fm := by
  constructor
  · intro h
    and_intros
    · intro m r hl; exact h (.binL _ _ _ _ hl)
    · intro m r hl; exact h (.binR _ _ _ _ hl)
  · intro ⟨h₁, h₂⟩ m r hl
    cases hl with
    | binL _ _ _ _ hl => exact h₁ hl
    | binR _ _ _ _ hl => exact h₂ hl

@[simp, grind =]
theorem Expr.original_cond_iff {n : Nat} {c et ef : Expr} {fm : FunMap n} :
    (c.cond et ef).Original fm ↔ c.Original fm ∧ et.Original fm ∧ ef.Original fm := by
  constructor
  · intro h
    and_intros
    · intro m r hl; exact h (.condC _ _ _ _ hl)
    · intro m r hl; exact h (.condT _ _ _ _ hl)
    · intro m r hl; exact h (.condF _ _ _ _ hl)
  · intro ⟨hc, het, hef⟩ m r hl
    cases hl with
    | condC _ _ _ _ hl => exact hc hl
    | condT _ _ _ _ hl => exact het hl
    | condF _ _ _ _ hl => exact hef hl

@[simp, grind =]
theorem Expr.original_proj_iff {n : Nat} {e : Expr} {i : Fin 2}
    {fm : FunMap n} : (e.proj i).Original fm ↔ e.Original fm := by
  constructor
  · intro h m r hl
    exact h (.proj _ _ _ hl)
  · intro h m r hl
    replace .proj _ _ _ hl := hl
    exact h hl

theorem Expr.original_mk {n : Nat} {e : Expr} (h : e.Bounded n) :
    e.Original (.mk n) := by
  intro m r hl
  refine ⟨h hl, ?_⟩
  intro k hk heq
  simp_all [FunMap.mk]

theorem Expr.original_update {n : Nat} {e : Expr} {fm : FunMap n} {m : Nat}
    (hm : m < n) (h : e.Original fm) : e.Original (fm.update m hm) := by
  intro k r hl
  exact FunMap.original_update hm (h hl)

def Expr.DeepOriginal (e : Expr) (p : Program) (fm : FunMap p.size) : Prop :=
  e.Original fm ∧ ∀ m, e.Reachable p m → ∃ hm, (p.fn[m]'hm).Original fm

@[grind →]
theorem Expr.DeepOriginal.validRefs {p : Program} {e : Expr} {fm : FunMap p.size}
    (h : e.DeepOriginal p fm) : e.ValidRefs p := h.1.bounded

@[grind .]
theorem Expr.DeepOriginal.deepValidFns {p : Program} {e : Expr}
    {fm : FunMap p.size} (h : e.DeepOriginal p fm) : e.DeepValidFns p :=
  fun _ hr => (h.2 _ hr).1

@[grind →]
theorem Expr.lt_of_deepOriginal_of_reachable {p : Program} {e : Expr}
    {fm : FunMap p.size} {n : Nat} (ho : e.DeepOriginal p fm)
    (hr : e.Reachable p n) : n < p.size :=
  (ho.2 _ hr).1

@[simp, grind =]
theorem Expr.deepOriginal_var_iff {p : Program} {n : Nat} {fm : FunMap p.size} :
    (var n).DeepOriginal p fm ↔ fm.Original n := by
  constructor <;> intro h
  · exact original_var_iff.mp h.1
  · exact ⟨original_var_iff.mpr h, nofun⟩

@[simp, grind =]
theorem Expr.deepOriginal_fn_iff {p : Program} {n : Nat} {fm : FunMap p.size} :
    (fn n).DeepOriginal p fm ↔ fm.Original n ∧ ∃ hn, (p.fn[n]'hn).DeepOriginal p fm := by
  grind [DeepOriginal]

@[simp, grind .]
theorem Expr.deepOriginal_const {p : Program} {c : Const} {fm : FunMap p.size} :
    (const c).DeepOriginal p fm :=
  ⟨original_const, fun _ hr => (not_reachable_const hr).elim⟩

@[simp, grind =]
theorem Expr.deepOriginal_bin_iff {p : Program} {k : BinKind} {e₁ e₂ : Expr} {fm : FunMap p.size} :
    (e₁.bin k e₂).DeepOriginal p fm ↔ e₁.DeepOriginal p fm ∧ e₂.DeepOriginal p fm := by
  grind [DeepOriginal]

@[simp, grind =]
theorem Expr.deepOriginal_cond_iff {p : Program} {c et ef : Expr} {fm : FunMap p.size} :
    (c.cond et ef).DeepOriginal p fm ↔
      c.DeepOriginal p fm ∧ et.DeepOriginal p fm ∧ ef.DeepOriginal p fm := by
  grind [DeepOriginal]

@[simp, grind =]
theorem Expr.deepOriginal_proj_iff {p : Program} {e : Expr} {i : Fin 2} {fm : FunMap p.size} :
    (e.proj i).DeepOriginal p fm ↔ e.DeepOriginal p fm := by
  grind [DeepOriginal]

theorem Expr.deepOriginal_mk {p : Program} {e : Expr} (hp : p.ValidRefs)
    (he : e.ValidRefs p) : e.DeepOriginal p (.mk _) := by
  constructor
  · exact original_mk he
  · intro m hr
    induction hr with
    | here e hl =>
      have hm := he hl
      exact ⟨hm, original_mk (hp hm)⟩
    | there e k hk hl hr ih => exact ih (hp hk)

def FunMap.LocalProvenance {n : Nat} (fm : FunMap n) (e e' : Expr) (k : Option Nat) :
    Prop :=
  ∀ ⦃m r⦄ (hm : fm.Dom m), e'.Local fm[m] r → m = k ∨ e.Local m r

structure FunMap.Valid {n : Nat} (fm : FunMap n) : Prop where
  lt : ∀ {m} (_ : m < n), fm[m] < n
  inj : ∀ {m k} (hm : fm.Dom m) (hk : fm.Dom k), fm[m] = fm[k] → m = k
  idem : ∀ {m} (_ : m < n), fm[fm[m]] = fm[m]

grind_pattern FunMap.Valid.lt =>
  fm.Valid, m < n, fm[m]
  where m =/= fm[_]'_

attribute [grind =] FunMap.Valid.idem

theorem FunMap.Valid.not_dom_map {n : Nat} {fm : FunMap n} (h : fm.Valid)
    {m : Nat} (hm : m < n) : ¬fm.Dom fm[m] := by
  rintro ⟨_, hne⟩
  exact hne (h.idem hm)

theorem FunMap.valid_mk {n : Nat} : (mk n).Valid := by
  constructor <;> grind

theorem FunMap.valid_update {n : Nat} {fm : FunMap n} {i : Nat}
    (hi : i < n) (hfm : fm.Original i) (h : fm.Valid) :
    (fm.update i hi).Valid := by
  constructor
  case lt =>
    intro k hk
    by_cases k = n
    · simp [*]
    · replace hk : k < n := by lia
      grind
  case inj => grind [h.inj]
  case idem =>
    intro m hm
    by_cases m = n
    · simp [*]
    · replace hm : m < n := by lia
      have := hfm.2 hm
      grind

structure FunMap.Extends {n' n : Nat} (fm' : FunMap n') (fm : FunMap n) : Prop where
  valid : fm'.Valid
  le : n ≤ n'
  eq : ∀ {m} (hm : fm.Dom m), fm'[m] = fm[m]
  eq_of_lt : ∀ {m} (_ : m < n'), fm'[m] < n → ∃ (_ : m < n), fm'[m] = fm[m]
  exists_of_ge : ∀ {m'}, n ≤ m' → m' < n' → ∃ (m : Nat) (_ : m < n), fm'[m] = m'

grind_pattern FunMap.Extends.eq =>
  fm'.Extends fm, fm.Dom m, fm'[m]

@[grind →]
theorem FunMap.dom_of_extends {n n' : Nat} {fm : FunMap n} {fm' : FunMap n'}
    {m : Nat} (hext : fm'.Extends fm) (h : fm.Dom m) : fm'.Dom m := by
  have := hext.eq h
  grind [Dom]

@[grind →]
theorem FunMap.dom_of_extends_of_lt {n n' : Nat} {fm : FunMap n}
    {fm' : FunMap n'} {m : Nat} (hext : fm'.Extends fm) (h : fm'.Dom m)
    (hlt : fm'[m] < n) : fm.Dom m := by
  have := hext.eq_of_lt h.1 hlt
  grind [Dom]

theorem FunMap.extends_self {n : Nat} {fm : FunMap n} (hfm : fm.Valid) :
    fm.Extends fm := by constructor <;> grind

@[grind →]
theorem FunMap.extends_trans {n₀ n₁ n₂ : Nat} {fm₀ : FunMap n₀}
    {fm₁ : FunMap n₁} {fm₂ : FunMap n₂} (h : fm₁.Extends fm₀)
    (h' : fm₂.Extends fm₁) : fm₂.Extends fm₀ := by
  have : ∀ m, fm₀.Dom m → fm₁.Dom m := fun m => dom_of_extends h
  obtain ⟨hfm₁, hle, h₀, h₁, h₂⟩ := h
  obtain ⟨hfm₂, hle', h₀', h₁', h₂'⟩ := h'
  constructor
  · exact hfm₂
  · grind
  · intro m hm hm'
    replace ⟨hm, heq'⟩ := h₁' hm (by lia)
    replace ⟨hm, heq⟩ := h₁ hm (heq' ▸ hm')
    exact ⟨hm, heq ▸ heq'⟩
  · intro m' hge hlt
    by_cases h : m' < n₁
    · obtain ⟨m, hm, hfmm⟩ := h₂ hge h
      have : fm₁.Dom m := ⟨by lia, by grind⟩
      exact ⟨m, hm, by grind⟩
    · simp only [Nat.not_lt] at h
      obtain ⟨m, hm, hfmm⟩ := h₂' h hlt
      by_cases h : m < n₀
      · exact ⟨m, h, hfmm⟩
      · simp only [Nat.not_lt] at h
        obtain ⟨k, hk, hfmk⟩ := h₂ h hm
        have : fm₁.Dom k := ⟨by lia, by grind⟩
        exact ⟨k, hk, by grind⟩
  · grind

theorem FunMap.extends_update {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n)
    (hfm : fm.Valid) (h : fm.Original m) (hfmm : ¬fm.Dom m) :
    (fm.update m hm).Extends fm := by
  constructor <;> grind [Dom, valid_update]

grind_pattern FunMap.extends_update => fm.Original m, fm.update m hm

theorem FunMap.original_of_extends {n n' : Nat} {fm : FunMap n} {fm' : FunMap n'}
    {m : Nat} (h : fm'.Extends fm) (ho : fm.Original m) : fm'.Original m := by
  obtain ⟨hm, ho⟩ := ho
  refine ⟨Nat.lt_of_lt_of_le hm h.le, ?_⟩
  intro k hk hfmk
  grind [h.eq_of_lt hk (hfmk ▸ hm)]

theorem Expr.original_of_extends {n n' : Nat} {e : Expr} {fm : FunMap n}
    {fm' : FunMap n'} (h : fm'.Extends fm) (ho : e.Original fm) :
    e.Original fm' := by
  intro m r hl
  exact FunMap.original_of_extends h (ho hl)

@[grind ⇐]
theorem Expr.deepOriginal_of_extends {p p' : Program} {e : Expr} {fm : FunMap p.size}
    {fm' : FunMap p'.size} (hpre : p.Prefix p') (hext : fm'.Extends fm)
    (ho : e.DeepOriginal p fm) : e.DeepOriginal p' fm' := by
  have ⟨ho, hor⟩ := ho
  refine ⟨Expr.original_of_extends hext ho, ?_⟩
  intro m hr
  grind [Expr.original_of_extends]

@[grind! .]
theorem FunMap.extends_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hfm : fm.Valid) (ho : e.DeepOriginal p fm) :
    (e.subst p vm fm).funMap.Extends fm := by
  fun_induction Expr.subst <;>
    try solve_by_elim [extends_self]
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih ⊢
    have hext := extends_update hm hfm (by grind) hfmm
    obtain ⟨hom, hm, ho⟩ := Expr.deepOriginal_fn_iff.mp ho
    apply extends_trans
    · exact hext
    · apply ih
      · exact valid_update hm hom hfm
      · exact Expr.deepOriginal_of_extends Program.prefix_push hext ho
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ h₁ hs₁ p₂ e₂' fm₂ h₂ hs₂ h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    dsimp only at ih₁ ih₂ ⊢
    obtain ⟨ho₁, ho₂⟩ := Expr.deepOriginal_bin_iff.mp ho
    have hext₁ := ih₁ hfm ho₁
    have hext₂ := ih₂ hext₁.valid (Expr.deepOriginal_of_extends h₁.pre hext₁ ho₂)
    exact extends_trans hext₁ hext₂
  next p vm fm c et ef p₁ c' fm₁ h₁ hs₁ vm₁ p₂ et' fm₂ h₂ hs₂ p₃ ef' fm₃ h₃ hs₃
      hf ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at ihc ihet ihef ⊢
    obtain ⟨hoc, hoet, hoef⟩ := Expr.deepOriginal_cond_iff.mp ho
    have hpre₂ := Program.prefix_trans h₁.pre h₂.pre
    have hext₁ := ihc hfm hoc
    have hext₂ := extends_trans hext₁ <|
      ihet hext₁.valid (Expr.deepOriginal_of_extends h₁.pre hext₁ hoet)
    exact extends_trans hext₂ <|
      ihef hext₂.valid (Expr.deepOriginal_of_extends hpre₂ hext₂ hoef)
  next p vm fm e i p' e' fm' h hs hf ih =>
    rw [hs] at ih
    dsimp at ih ⊢
    exact ih hfm (Expr.deepOriginal_proj_iff.mp ho)

theorem FunMap.valid_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (h : fm.Valid) (ho : e.DeepOriginal p fm) :
    (e.subst p vm fm).funMap.Valid :=
  (extends_subst h ho).valid

grind_pattern FunMap.valid_subst => (e.subst p vm fm).funMap

structure VarMap.Valid {n : Nat} (vm : VarMap n) (fm : FunMap n) : Prop where
  bounded : ∀ {m} (_ : m < n), vm[m].Bounded n
  localProvenance : ∀ {m} (hm : fm.Dom m),
    fm.LocalProvenance (.var m) vm[m] none
  original : ∀ {m} (hm : vm.Dom m), ¬fm.Dom m → vm[m].Original fm

attribute [grind! .] VarMap.Valid.bounded

theorem VarMap.valid_mk {n m : Nat} {v : Expr} (hv : v.Bounded n) :
    (mk n m v).Valid (.mk n) := by
  constructor <;> grind [FunMap.Dom, Expr.original_mk]

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
    intro m hfmm n r hfmn hl
    have hm : m < p.size := by grind
    have hn : n < p.size := by grind
    by_cases i = m
    · grind
    · have : i ≠ n := by grind
      apply hvm.localProvenance <;> grind
  case original => grind [Expr.original_update, hvm.original]

theorem VarMap.valid_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (ho : e.DeepOriginal p fm) :
    vm.extend.Valid (e.subst p vm fm).funMap := by
  fun_induction Expr.subst <;> try grind
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    obtain ⟨hom, hm, ho⟩ := Expr.deepOriginal_fn_iff.mp ho
    have hvm₁ : vm₁.Valid fm₁ := valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm hom hfm
    have hext₁ := FunMap.extends_update hm hfm hom hfmm
    replace ho : p.fn[m].DeepOriginal p₁ fm₁ :=
      Expr.deepOriginal_of_extends Program.prefix_push hext₁ ho
    have hvm₂ : vm₁.extend.Valid fm₂ :=
      ih hvm₁ hfm₁ ho
    have hfm₂ : fm₂.Valid := by grind
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hext := FunMap.extends_trans hext₁ hext₂
    constructor
    case bounded => grind
    case localProvenance =>
      intro k hfmk l r hfml hlc
      by_cases hk : k < p.size
      · simp only [VarMap.getElem_extend_lt, *] at hlc
        by_cases hmk : m = k
        · subst k
          have hl' : fm₂[l] < p.size := hvm.bounded hm hlc
          obtain ⟨hl, heq⟩ := hext.eq_of_lt hfml.1 hl'
          rw [heq] at hlc
          by_cases hvmm : vm.Dom m
          · grind [hvm.original hvmm hfmm hlc]
          · grind [Dom]
        · apply hvm₂.localProvenance hfmk hfml
          simp [vm₁, show k < p.size + 1 by lia, *]
      · apply hvm₂.localProvenance hfmk hfml
        simp only [Nat.not_lt] at hk
        simpa [vm₁, show p.size + 1 ≤ k by grind, *] using hlc
    case original =>
      intro k hvmk hfmk
      dsimp only at hfmk
      by_cases hk : k < p.size
      · replace hfmk : ¬fm.Dom k := by grind
        simp only [getElem_extend_lt, hk]
        exact Expr.original_of_extends hext (hvm.original (by grind) hfmk)
      · grind

grind_pattern VarMap.valid_subst =>
  vm.extend (n' := (e.subst p vm fm).program.size)

theorem Expr.validRefs_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (he : e.DeepOriginal p fm) :
    let ⟨p', e', _, _⟩ := e.subst p vm fm
    e'.ValidRefs p' := by
  fun_induction subst with grind

theorem Expr.localProvenance_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (ho : e.DeepOriginal p fm) :
    let ⟨_, e', fm', _⟩ := e.subst p vm fm
    fm'.LocalProvenance e e' none := by
  fun_induction Expr.subst
  next p e vm fm h =>
    intro n r hn hl
    have := (ho.1 hl).map
    contradiction
  next p vm fm m h =>
    intro n r hn hl
    have hm : m < p.size := by grind
    simp only [hm, getElem?_pos, Option.getD_some] at hl
    by_cases hfmm : fm.Dom m
    · exact hvm.localProvenance hfmm hn hl
    · simp only [free_in_var_iff, forall_eq, Classical.not_not] at h
      grind [hvm.original h hfmm hl]
  next p vm fm m hm hfmm hf =>
    intro n r hfmn hl
    grind [hfm.inj]
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih ⊢
    have hext₁ : fm₁.Extends fm := by grind
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm (by grind) hfm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := hext₂.valid
    intro n r hfmn hl
    subst e'
    simp only [local_fn_iff] at hl
    obtain ⟨hr, hmn'⟩ := hl
    have : fm₂[m] = m' := by grind
    rw [← this] at hmn'
    grind [hfm₂.inj (by grind) hfmn hmn']
  next => grind
  next p vm fm b h => simp [FunMap.LocalProvenance]
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ h₁ hs₁ p₂ e₂' fm₂ h₂ hs₂ h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    dsimp only at *
    have hvm₁ : vm.extend.Valid fm₁ := by grind
    have hfm₁ : fm₁.Valid := by grind
    obtain ⟨ho₁, ho₂⟩ := Expr.deepOriginal_bin_iff.mp ho
    have hf' := ih₁ hvm hfm ho₁
    have he' := ih₂ hvm₁ hfm₁ (deepOriginal_of_extends (by grind) (by grind) ho₂)
    intro n r hfmn hl
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hv₁' : e₁'.ValidRefs p₁ := by grind [validRefs_subst]
    obtain hl | hl := Expr.local_bin_iff.mp hl
    · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hfmn.1 (hv₁' hl)
      rw [heq] at hl
      replace hfmn : fm₁.Dom n := by grind
      have := hf' hfmn hl
      grind
    · have := he' hfmn hl
      grind
  next p vm fm c et ef p₁ c' fm₁ h₁ hs₁ vm₁ p₂ et' fm₂ h₂ hs₂ p₃ ef' fm₃ h₃ hs₃
      hf ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at ihc ihet ihef ⊢
    have hvm₁ : vm₁.Valid fm₁ := by grind
    have hfm₁ : fm₁.Valid := by grind
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind
    have hfm₂ : fm₂.Valid := by grind
    obtain ⟨hoc, hoet, hoef⟩ := Expr.deepOriginal_cond_iff.mp ho
    have hc' := ihc hvm hfm hoc
    have het' := ihet hvm₁ hfm₁
      (deepOriginal_of_extends (by grind) (by grind) hoet)
    have hef' := ihef hvm₂ hfm₂
      (deepOriginal_of_extends (by grind) (by grind) hoef)
    intro n r hfmn hl
    have hext₁ : fm₃.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    have hvc' : c'.ValidRefs p₁ := by grind [validRefs_subst]
    have hvet' : et'.ValidRefs p₂ := by
      grind [validRefs_subst]
    obtain hl | hl | hl := Expr.local_cond_iff.mp hl
    · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hfmn.1 (hvc' hl)
      rw [heq] at hl
      have := hc' (by grind) hl
      grind
    · replace ⟨hn, heq⟩ := hext₂.eq_of_lt hfmn.1 (hvet' hl)
      rw [heq] at hl
      have := het' (by grind [FunMap.Dom]) hl
      grind
    · have := hef' hfmn hl
      grind
  next p vm fm e i p' e' fm' h hs hf ih =>
    rw [hs] at ih
    dsimp only at ih ⊢
    intro n r hfmn hl
    rw [Expr.local_proj_iff] at hl ⊢
    apply ih hvm hfm <;> grind

theorem Program.validRefs_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (ho : e.DeepOriginal p fm) : (e.subst p vm fm).program.ValidRefs := by
  fun_induction Expr.subst <;> try simpa using hp
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih ⊢
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm (by grind) hfm
    have hp₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind)) (by grind)
    have hf' : f'.ValidRefs p₂ := by grind [Expr.validRefs_subst]
    exact validRefs_setBody (by grind) hp₂ hf'
  next => grind
  next => grind
  next => grind

structure Program.ValidSubst (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) where
  fn_localProvenance : ∀ {m} (hm : fm.Dom m) (hm' : fm[m] < p.size),
    fm.LocalProvenance p.fn[m] p.fn[fm[m]] m
  nests_of_dom : ∀ {m}, fm.Dom m → ∃ n, vm.Dom n ∧ n ≻[p] m
  dom_of_nests : ∀ {n m}, vm.Dom n → n ≻[p] m → vm.Dom m → fm.Dom m
  compat : ∀ {m} (hm : fm.Dom m), vm.Dom m → vm[m] = .var fm[m]

theorem Program.validSubst_mk {p : Program} {n : Nat} {v : Expr} (hwf : p.WF) :
    p.ValidSubst (.mk _ n v) (.mk _) := by
  constructor <;> grind [VarMap.Dom, FunMap.Dom, WF]

theorem Program.validSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {l i : Nat} (hi : i < p.size) (hfm : fm.Valid)
    (hp : p.ValidRefs) (hvml : vm.Dom l) (hnestsi : l ≻[p] i)
    (hvalid : p.ValidSubst vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).ValidSubst
      (vm.update i hi) (fm.update i hi) := by
  constructor
  case fn_localProvenance =>
    intro m hfmm hm' n r hfmn hl
    by_cases hnm : n = m
    · simp [*]
    · right
      replace hm : m < p.size := by grind
      replace hn : n < p.size := by grind
      have hm' := hfm.lt hm
      have hn' := hfm.lt hn
      have him : i ≠ m := by grind
      have hin : i ≠ n := by grind
      replace hfmm : fm.Dom m := by grind
      replace hfmn : fm.Dom n := by grind
      have := hvalid.fn_localProvenance hfmm hm' hfmn (by simpa [*] using hl)
      simpa [*]
  case nests_of_dom => grind [hvalid.nests_of_dom]
  case dom_of_nests => grind [hvalid.dom_of_nests]
  case compat => grind [hvalid.compat]

theorem Program.validSubst_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    p'.ValidSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hvalid
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih
    simp only [Classical.not_forall, Classical.not_not] at hf
    obtain ⟨l, hf, hvml⟩ := hf
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hvml.1 hm hne hf
    have hext₁ : fm₁.Extends fm := FunMap.extends_update hm hfm (by grind) hfmm
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := hext₁.valid
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind [VarMap.valid_subst]
    have hfm₂ : fm₂.Valid := by grind
    have hvalid₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
      (validSubst_push_recurse hm hfm hp hvml hnestsm hvalid) (by grind)
    have hext := FunMap.extends_trans hext₁ hext₂
    have hprov : fm₂.LocalProvenance p.fn[m] f' none := by
      grind [Expr.localProvenance_subst]
    have hpre : p.Prefix p₃ := by grind
    constructor
    case fn_localProvenance =>
      intro n hfmn hn' k r hfmk hl
      have hfmm : fm₂[m] = m' := by grind [hext₂.eq]
      by_cases hnm : m = n
      · subst n
        simp only [Vector.getElem_set_self, p₃, hfmm] at hl
        replace hl := hprov hfmk hl
        simp only [reduceCtorEq, false_or] at hl
        have heq : p₂.fn[m] = p.fn[m] := by
          have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [prefix_subst.fn_eq (by lia)]
          simp [p₁, hm]
        simp [p₃, hfmm ▸ hfmn.2, *]
      · have hnm' : fm₂[n] ≠ m' := by
          intro heq
          rw [← heq] at hfmm
          have := hfm₂.inj (by grind) (by grind) hfmm
          contradiction
        simp only [ne_eq, not_false_eq_true, Ne.symm, Vector.getElem_set_ne, p₃, hnm'] at hl
        have hne : m' ≠ n := by grind
        cases hvalid₂.fn_localProvenance hfmn hn' hfmk hl <;> simp [p₃, *]
    case nests_of_dom =>
      have hnestsm₃ : l ≻[p₃] m := by grind
      intro n hfmn
      by_cases m = n
      · subst n
        grind
      · obtain ⟨k, hvmk, hnests⟩ := hvalid₂.nests_of_dom hfmn
        have hb : p₂.fn[m'] = Expr.recurse m' := by
          have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [prefix_subst.fn_eq (by lia)]
          grind
        replace hnests : k ≻[p₃] n := nests_in_setBody (by grind) (by grind) hnests
        grind
    case dom_of_nests =>
      intro n k hvmn hnests hvmk
      by_cases hk : k < p.size
      · replace hnests : n ≻[p] k := by grind
        have := hvalid.dom_of_nests (by grind) hnests (by grind)
        grind
      · grind
    case compat =>
      intro k hfmk hvmk
      have hfmm : ¬fm.Dom m := by grind
      have := hvalid₂.compat hfmk (by grind)
      by_cases m = k
      · subst k
        have := hvalid.dom_of_nests hvml hnestsm (by grind)
        contradiction
      · grind
  next => grind [validRefs_subst]
  next => grind [validRefs_subst]
  next => grind [validRefs_subst]

theorem Program.exists_of_ge_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hfm : fm.Valid)
    (ho : e.DeepOriginal p fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    n' < p'.size → ∃ (n : Nat) (hn : n < p.size), fm'[n] = n' := by
  intro hlt
  have hext : (e.subst p vm fm).funMap.Extends fm := FunMap.extends_subst hfm ho
  obtain ⟨n, hn, hfmn⟩ := hext.exists_of_ge hn' hlt
  grind

theorem Program.pathWithout_of_pathWithout_in_subst_of_ge {p : Program}
    {e : Expr} {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) {n' m' k' : Nat} (hn' : p.size ≤ n')
    (hm' : p.size ≤ m') (hk' : p.size ≤ k') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    n' < p'.size → m' < p'.size → k' < p'.size → m' ⟶[p', n']* k' →
      ∃ (n m k : Nat) (hn : n < p.size) (hm : m < p.size) (hk : k < p.size),
        fm'[n] = n' ∧ fm'[m] = m' ∧ fm'[k] = k' ∧ m ⟶[p, n]* k := by
  intro hnlt hmlt hklt hp'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have h' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  induction hp' with
  | refl m' hne' =>
    obtain ⟨n, hn, hfmn⟩ := exists_of_ge_in_subst hfm ho hn' hnlt
    obtain ⟨m, hm, hfmm⟩ := exists_of_ge_in_subst hfm ho hm' hmlt
    have hne : n ≠ m := by grind
    exact ⟨n, m, m, hn, hm, hm, hfmn, hfmm, hfmm, .refl _ hne⟩
  | step m' l' k' hne' hs' hp' ih =>
    obtain ⟨m, hm, hmm'⟩ := exists_of_ge_in_subst hfm ho hm' hmlt
    have hl' : p.size ≤ l' := by grind
    obtain ⟨_, hlf'⟩ := hs'
    have hllt : l' < p'.size := by grind
    have ⟨n, l, k, hn, hl, hk, hnn', hll', hkk', hp⟩ := ih hl' hk' hllt hklt
    replace hlf' : p'.fn[fm'[m]].LocalFn fm'[l] := by grind
    have hne : n ≠ m := by grind
    have hfmm : fm'.Dom m := ⟨by lia, by grind⟩
    have hfml : fm'.Dom l := ⟨by lia, by grind⟩
    have hlf := h'.fn_localProvenance hfmm (hmm' ▸ hmlt) hfml hlf'
    simp only [Option.some.injEq, prefix_subst.fn_eq hm, p'] at hlf
    obtain heq | hlf := hlf
    · grind
    · exact ⟨n, m, k, hn, hm, hk, hnn', hmm', hkk', .step _ _ _ hne ⟨hm, hlf⟩ hp⟩

theorem Program.free_in_fn_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) {n' m' : Nat} (hn' : p.size ≤ n')
    (hm' : p.size ≤ m') (hne' : n' ≠ m') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    ∀ (_ : m' < p'.size), p'.fn[m'].Free p' n' →
      ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
        fm'[n] = n' ∧ fm'[m] = m' ∧ p.fn[m].Free p n := by
  intro hmlt hf'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have h' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  obtain ⟨k', hklt, hlv', hp'⟩ := (free_in_fn_iff hmlt hne').mp hf'
  have hk' : p.size ≤ k' := by grind [prefix_subst.fn_eq]
  have hnlt : n' < p'.size := by grind
  obtain ⟨n, m, k, hn, hm, hk, hnn', hmm', hkk', hp⟩ :=
    pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp hvalid ho hn' hm' hk' hnlt hmlt hklt hp'
  replace hlv' : p'.fn[fm'[k]].LocalVar fm'[n] := by grind
  have hne : n ≠ m := by grind
  have hfmk : fm'.Dom k := ⟨by lia, by grind⟩
  have hfmn : fm'.Dom n := ⟨by lia, by grind⟩
  have hlv := h'.fn_localProvenance hfmk (hkk' ▸ hklt) hfmn hlv'
  rw [prefix_subst.fn_eq hk] at hlv
  simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
  exact ⟨n, m, hn, hm, hnn', hmm', (free_in_fn_iff hm hne).mpr ⟨k, hk, hlv, hp⟩⟩

theorem Expr.free_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', e', fm', _⟩ := e.subst p vm fm
    e'.Free p' n' → ∃ (n : Nat) (_ : n < p.size),
      fm'[n] = n' ∧ e.Free p n := by
  intro hf
  let p' := (e.subst p vm fm).program
  let e' := (e.subst p vm fm).expr
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := Program.validRefs_subst hvm hfm hp ho
  have h' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  have hlt : n' < p'.size :=
    lt_size_of_free hvp' (validRefs_subst hvm hfm ho) hf
  obtain ⟨n, hn, heq⟩ := Program.exists_of_ge_in_subst hfm ho hn' hlt
  obtain hlv' | ⟨m', k', hk', hlf', hp', hlv'⟩ := free_iff.mp hf
  · refine ⟨n, hn, heq, free_of_localVar ?_⟩
    have hfmn : fm'.Dom n := ⟨by lia, by grind⟩
    simpa using localProvenance_subst hvm hfm ho hfmn (heq ▸ hlv')
  · have hklt : k' < p'.size := by grind
    by_cases hm' : m' < p.size
    · grind [Program.prefix_subst.fn_eq]
    · simp only [Nat.not_lt] at hm'
      have hk' : p.size ≤ k' := by grind [Program.prefix_subst.fn_eq]
      obtain ⟨n, m, k, hn, hm, hk, hnn', hmm', hkk', hp⟩ :=
        Program.pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp hvalid ho hn' hm' hk'
          ‹_› (validRefs_subst hvm hfm ho hlf') ‹_› hp'
      replace hlf' : e'.LocalFn fm'[m] := by grind
      replace hlv' : p'.fn[fm'[k]].LocalVar fm'[n] := by grind
      have hfmn : fm'.Dom n := ⟨by lia, by grind⟩
      have hfmm : fm'.Dom m := ⟨by lia, by grind⟩
      have hfmk : fm'.Dom k := ⟨by lia, by grind⟩
      have hlf := localProvenance_subst hvm hfm ho hfmm hlf'
      simp only [reduceCtorEq, false_or] at hlf
      have hlv := h'.fn_localProvenance hfmk (hkk' ▸ hklt) hfmn hlv'
      rw [Program.prefix_subst.fn_eq hk] at hlv
      simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
      exact ⟨n, hn, hnn', free_iff.mpr <| Or.inr ⟨m, k, hk, hlf, hp, hlv⟩⟩

theorem Program.nests_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {m n : Nat} (hn : n < p.size)
    (hp : p.ValidRefs) (h : m ≻[(e.subst p vm fm).program] n) :
    m ≻[p] n := (nests_in_prefix_iff hn hp prefix_subst).mp h

theorem Program.nests_of_nests_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (h : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) {n' m' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    n' ≻[p'] m' → ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
      fm'[n] = n' ∧ fm'[m] = m' ∧ n ≻[p] m := by
  intro hnests'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst hvm hfm hp h ho
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  induction hnests' with
  | free n' m' hltn hltm hne' hf' =>
    have hm' : p.size ≤ m' := by grind
    obtain ⟨n, m, hn, hm, hfmn, hfmm, hf⟩ :=
      Program.free_in_fn_of_free_in_subst_of_ge hvm hfm hp h ho hn' hm' hne' hltm hf'
    have hne : n ≠ m := by grind
    exact ⟨n, m, hn, hm, hfmn, hfmm, .free _ _ hn hm hne hf⟩
  | trans n' k' m' hnests₁' hnests₂' ih₁ ih₂ =>
    have hk' : p.size ≤ k' := by grind
    obtain ⟨n, k, hn, hk, hnn', hkk', hnests₁⟩ := ih₁ hn'
    obtain ⟨l, m, hl, hm, hll', hmm', hnests₂⟩ := ih₂ hk'
    have hfmk : fm'.Dom k := ⟨by grind, by grind⟩
    have hfml : fm'.Dom l := ⟨by grind, by grind⟩
    obtain rfl : k = l := hfm'.inj hfmk hfml (by simp [fm', hkk', hll'])
    exact ⟨n, m, hn, hm, hnn', hmm', .trans _ _ _ hnests₁ hnests₂⟩

theorem Program.subst_wf {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (h : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) (hwf : p.WF) :
    (e.subst p vm fm).program.WF := by
  intro m hnests
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  by_cases hm : m < p.size
  · exact hwf <| nests_of_nests_in_subst_of_lt hm hp hnests
  · simp only [Nat.not_lt] at hm
    have hvalid' : p'.ValidSubst vm.extend fm' := validSubst_subst hvm hfm hp h ho
    have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
    replace ⟨k, l, hk, hl, hkk', hll', hnests⟩ :=
      nests_of_nests_in_subst_of_ge hvm hfm hp h ho hm hnests
    have hfmk : fm'.Dom k := ⟨by grind, by grind⟩
    have hfml : fm'.Dom l := ⟨by grind, by grind⟩
    obtain rfl : k = l := hfm'.inj hfmk hfml (by simp [fm', hkk', hll'])
    exact hwf hnests

def Expr.WFSubst (e : Expr) (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃n m⦄, n ≻[p] m → e.Free p m → vm.Dom n → vm.Dom m ∧ fm.Dom m

@[grind =]
theorem Expr.wfSubst_bin_iff {k : BinKind} {e₁ e₂ : Expr} {p : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    (e₁.bin k e₂).WFSubst p vm fm ↔ e₁.WFSubst p vm fm ∧ e₂.WFSubst p vm fm := by
  grind [WFSubst]

@[grind =]
theorem Expr.wfSubst_cond_iff {c et ef : Expr} {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} :
    (c.cond et ef).WFSubst p vm fm ↔
      c.WFSubst p vm fm ∧ et.WFSubst p vm fm ∧ ef.WFSubst p vm fm := by
  grind [WFSubst]

@[grind =]
theorem Expr.wfSubst_proj_iff {e : Expr} {i : Fin 2} {p : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    (e.proj i).WFSubst p vm fm ↔ e.WFSubst p vm fm := by
  grind [WFSubst]

theorem Expr.wfSubst_in_subst {p : Program} {e₁ e₂ : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hfm : fm.Valid) (hp : p.ValidRefs)
    (he₁ : e₁.ValidRefs p) (ho : e₂.DeepOriginal p fm)
    (h : e₁.WFSubst p vm fm) :
    let ⟨p', _, fm', _⟩ := e₂.subst p vm fm
    e₁.WFSubst p' vm.extend fm' := by
  grind [WFSubst]

theorem Expr.exists_free_subst_var {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n m : Nat} {r : RefKind} (he : e.ValidRefs p)
    (hwfs : e.WFSubst p vm fm) (hvmn : vm.Dom n)
    (hnests : n ≻[p] m) (hl : e.Local m r) :
    ∃ (k : Nat), vm.Dom k ∧ e.Free p k := by
  have hm := he hl
  cases r with
  | var =>
    have hf : e.Free p m := Expr.free_of_localVar hl
    obtain ⟨hvmm, -⟩ := hwfs hnests hf hvmn
    exact ⟨m, hvmm, hf⟩
  | fn =>
    obtain ⟨_, k, hk, hne, hf, hnests⟩ := Program.nests_iff.mp hnests
    replace hf := free_of_localFn_of_free _ hne hl hf
    cases hnests with
    | refl _ => exact ⟨n, hvmn, hf⟩
    | nests _ hnests =>
      obtain ⟨hvmk, -⟩ := hwfs hnests hf hvmn
      exact ⟨k, hvmk, hf⟩

def FunMap.StrongProvenance (p : Program) (fm : FunMap p.size)
    (vm : VarMap p.size) (e e' : Expr) (k : Option Nat) : Prop :=
  ∀ ⦃m' r⦄ (_ : m' < p.size),
    e'.Local m' r →
      ∃ (m : Nat) (_ : m < p.size),
        ¬fm.Dom m ∧ (∀ k, vm.Dom k → k ⊁[p] m) ∧
          (e.LocalVar m ∧ vm[m].Local m' r ∨ e.LocalFn m ∧ m' = m ∧ r = .fn) ∨
          fm[m] = m' ∧ (m = k ∨ e.Local m r ∧ fm.Dom m)

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
    (hwf : p.WF) (ho : e.DeepOriginal p fm) (hwfe : e.WFSubst p vm fm) :
    let ⟨p', e', fm', _⟩ := e.subst p vm fm
    fm'.StrongProvenance p' vm.extend e e' none := by
  fun_induction subst
  next p e vm fm h =>
    intro n r hn hl
    have hnnests : ∀ m, vm.Dom m → m ⊁[p] n := by
      intro m hvmm hnests
      obtain ⟨k, hvmk, hf⟩ :=
        exists_free_subst_var ho.validRefs hwfe hvmm hnests hl
      have := h k hf
      contradiction
    have hfmn : ¬fm.Dom n := by
      intro hfmn
      obtain ⟨m, hvmm, hnests⟩ := hvalid.nests_of_dom hfmn
      exact hnnests m hvmm hnests
    refine ⟨n, hn, Or.inl ⟨hfmn, by grind, ?_⟩⟩
    cases r with
    | var =>
      have hf := h _ (free_of_localVar hl)
      exact Or.inl ⟨hl, by simp_all [VarMap.Dom]⟩
    | fn => exact Or.inr ⟨hl, rfl, rfl⟩
  next p vm fm m hvmm =>
    intro n r hn hl
    simp only [free_in_var_iff, forall_eq, Classical.not_not] at hvmm
    have hm := hvmm.1
    simp only [getElem?_pos, Option.getD_some, hm] at hl
    by_cases hfmk : fm.Dom m
    · refine ⟨m, hm, Or.inr ?_⟩
      have := hvalid.compat hfmk hvmm
      grind
    · refine ⟨m, hm, Or.inl ⟨hfmk, ?_, Or.inl ⟨.var, by grind⟩⟩⟩
      intro l hvml hnests
      exact hfmk <| hvalid.dom_of_nests (by grind) hnests hvmm
  next p vm fm m hm hfmm hf =>
    intro n r hn hl
    simp only [local_fn_iff] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨m, hm, Or.inr ⟨rfl, Or.inr ⟨.fn, hfmm⟩⟩⟩
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    intro m'' r hm' hl
    simp only [Expr.local_fn_iff, e'] at hl
    obtain ⟨hr, rfl⟩ := hl
    have hext : fm₂.Extends fm₁ := by grind [FunMap.valid_update]
    exact ⟨m, by lia, Or.inr (by grind [hext.eq])⟩
  next p vm fm m hm h =>
    intro m' r hm' hl
    simp only [local_fn_iff] at hl
    lia
  next p vm fm c h =>
    intro m' r hm' hl
    simp at hl
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ h₁ hs₁ p₂ e₂' fm₂ h₂ hs₂ h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    dsimp only at *
    have hp₁ : p₁.ValidRefs := by grind [Program.validRefs_subst]
    have hvalid₂ : p₂.ValidSubst vm.extend fm₂ := by
      grind [Program.validSubst_subst]
    have he₁' : fm₁.StrongProvenance p₁ vm.extend e₁ e₁' none := by grind
    have he₂' : fm₂.StrongProvenance p₂ vm.extend e₂ e₂' none := by
      grind [wfSubst_in_subst, Program.validSubst_subst, Program.subst_wf]
    have hext : fm₂.Extends fm₁ := by grind
    replace he₁' : fm₂.StrongProvenance p₂ vm.extend e₁ e₁' none := by
      intro n r hn hl
      replace hn : n < p₁.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hfmm, hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := he₁' hn hl
      · replace hfmm : ¬fm₂.Dom m := by grind [hvalid₂.nests_of_dom]
        exact ⟨m, by grind, Or.inl ⟨hfmm, by grind, by grind⟩⟩
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    exact FunMap.strongProvenance_bin he₁' he₂'
  next p vm fm c et ef p₁ c' fm₁ h₁ hs₁ vm₁ p₂ et' fm₂ h₂ hs₂ p₃ ef' fm₃ h₃ hs₃
      hf ihc ihet ihef =>
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
      grind [wfSubst_in_subst, Program.validRefs_subst,
        Program.validSubst_subst, Program.subst_wf]
    have hef' : fm₃.StrongProvenance p₃ vm.extend ef ef' none := by
      grind [wfSubst_in_subst, Program.validRefs_subst,
        Program.validSubst_subst, Program.subst_wf]
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    replace hc' : fm₃.StrongProvenance p₃ vm.extend c c' none := by
      intro n r hn hl
      replace hn : n < p₁.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hfmm, hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := hc' hn hl
      · replace hfmm : ¬fm₃.Dom m := by grind [hvalid₃.nests_of_dom]
        exact ⟨m, by grind, Or.inl ⟨hfmm, by grind, by grind⟩⟩
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    replace het' : fm₃.StrongProvenance p₃ vm.extend et et' none := by
      intro n r hn hl
      replace hn : n < p₂.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hfmm, hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := het' hn hl
      · replace hfmm : ¬fm₃.Dom m := by grind [hvalid₃.nests_of_dom]
        exact ⟨m, by grind, Or.inl ⟨hfmm, by grind, by grind⟩⟩
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    exact FunMap.strongProvenance_cond hc' het' hef'
  next p vm fm e i p' e' fm' h hs hf ih =>
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
  ∀ ⦃m⦄ (hm : fm.Dom m) (_ : fm[m] < p.size),
    fm.StrongProvenance p vm p.fn[m] p.fn[fm[m]] m

theorem Program.wfSubst_fn_mk {p : Program} {n : Nat} {v : Expr}
    (hn : n < p.size) (hwf : p.WF) :
    p.fn[n].WFSubst p (.mk _ n v) (.mk _) := by
  intro k m hnests hf hvmk
  obtain rfl : n = k := by grind
  exfalso
  by_cases h : m = n
  · subst m
    exact hwf hnests
  · exact hwf (nests_iff.mpr ⟨hvmk.1, _, by grind, h, hf, .nests _ hnests⟩)

theorem Program.wfSubst_mk {p : Program} {n : Nat} {v : Expr} :
    p.WFSubst (.mk _ n v) (.mk _) := by
  grind [WF, WFSubst]

theorem Program.wfSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} (hfm : fm.Valid) (hp : p.ValidRefs) {l i : Nat}
    (hi : i < p.size) (hvml : vm.Dom l) (hfmi : ¬fm.Dom i) (hnestsi : l ≻[p] i)
    (hwfs : p.WFSubst vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).WFSubst
      (vm.update i hi) (fm.update i hi) := by
  intro m hfmm hm'
  by_cases m = p.size
  · grind
  · replace hm : m < p.size := by grind
    by_cases i = m
    · intro n r hn hlc
      grind
    · intro n r hn hlc
      replace hm' : fm[m] < p.size := by grind
      replace hn : n < p.size := by grind
      obtain ⟨k, hk, ⟨hvmk, hnnests, hlc⟩ | ⟨hfmk, heq | ⟨hlc, h⟩⟩⟩ :=
        hwfs (by grind) hm' hn (by simpa [*] using hlc)
      · have : i ≠ k := by grind
        exact ⟨k, by lia, Or.inl ⟨by grind, by grind, by simp [*]⟩⟩
      · grind
      · have : i ≠ k := by grind
        exact ⟨k, by lia, by grind⟩

theorem Program.wfSubst_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm) (hwf : p.WF)
    (ho : e.DeepOriginal p fm) (hwfs : p.WFSubst vm fm)
    (hwfe : e.WFSubst p vm fm) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    p'.WFSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hwfs
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at *
    simp only [Classical.not_forall, Classical.not_not] at hf
    obtain ⟨l, hf, hvml⟩ := hf
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hvml.1 hm hne hf
    obtain ⟨hom, hm, ho⟩ := Expr.deepOriginal_fn_iff.mp ho
    have ho' : p.fn[m].DeepOriginal p₁ fm₁ := by grind
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm hom hfm
    have hp₁ : p₁.ValidRefs := validRefs_push hp (by grind)
    have hvalid₁ : p₁.ValidSubst vm₁ fm₁ :=
      validSubst_push_recurse hm hfm hp hvml hnestsm hvalid
    have hwf₁ : p₁.WF := push_wf hp hwf
    have hwfs₁ : p₁.WFSubst vm₁ fm₁ :=
      wfSubst_push_recurse hfm hp hm hvml hfmm hnestsm hwfs
    have hwfsm : p.fn[m].WFSubst p₁ vm₁ fm₁ := by
      intro n k hnests hf hvmn
      by_cases m = k
      · grind
      · have hn : n < p.size := by grind
        replace hfmm : fm₁.Dom m := by grind
        replace hnests : n ≻[p] k := by grind
        replace hf : p.fn[m].Free p k := by grind
        replace hk : k < p.size := Expr.lt_size_of_free hp (hp hm) hf
        have hmn : m ≠ n := by
          intro rfl
          exfalso
          exact hwf (nests_iff.mpr ⟨hm, _, hk, ‹m ≠ k›.symm, hf, .nests _ hnests⟩)
        grind [hwfe hnests (.fn _ hm ‹m ≠ k›.symm hf) (by grind)]
    have hwfs₂ := ih hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ ho' hwfs₁ hwfsm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := hext₂.valid
    have hmm' : fm₂[m] = m' := by grind [hext₂.eq]
    have hfmm' : fm₂[m'] = m' := by grind
    have hpre₂ : p.Prefix p₂ := prefix_trans prefix_push h₂.pre
    have hpre₃ : p.Prefix p₃ := by grind
    intro n hfmn hn'
    replace hn : n < p.size := by
      false_or_by_contra
      have hn' : p₁.size ≤ n := by grind
      obtain ⟨k, hk, hfmk⟩ :=
        exists_of_ge_in_subst (vm := vm₁) hfm₁ ho' hn' (by grind)
      have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
      subst p₂
      have hfm₂ : fm₂ = (p.fn[m].subst p₁ vm₁ fm₁).funMap := by grind
      subst fm₂
      exact hfm₂.not_dom_map (by grind) (hfmk ▸ hfmn)
    by_cases m = n
    · subst n
      simp only [ne_eq, show m' ≠ m by lia, not_false_eq_true, Vector.getElem_set_ne,
        Vector.getElem_set_self, p₃, hmm']
      have hf' := Expr.strongProvenance_subst hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ ho' hwfsm
      rw [hs₂] at hf'
      dsimp only at hf'
      rw [show p₂.fn[m] = p.fn[m] by grind]
      intro k r hk hlc
      obtain ⟨l, hl', ⟨hll', hnnests, h⟩ | ⟨hfml, h | ⟨hlc, h⟩⟩⟩ := hf' hk hlc
      · have hl : l < p.size := by grind
        by_cases m = l
        · exact ⟨m, by lia, Or.inr (by grind)⟩
        · exact ⟨l, hl', Or.inl ⟨hll', by grind, by grind⟩⟩
      · contradiction
      · exact ⟨l, hl', Or.inr ⟨hfml, Or.inr ⟨hlc, h⟩⟩⟩
    · have : m' ≠ n := by grind
      have : m' ≠ fm₂[n] := by
        intro h
        have := hfm₂.inj (by grind) hfmn (hmm' ▸ h)
        contradiction
      simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, p₃, *]
      intro k r hk hlc
      obtain ⟨l, hl, ⟨hmm', hnnests, h⟩ | ⟨hfml, h | ⟨hlc, h⟩⟩⟩ :=
        hwfs₂ hfmn (by lia) hk hlc
      · by_cases m = l
        · exact ⟨m, by lia, Or.inr (by grind)⟩
        · have : vm₁.extend[l] = vm.extend[l] := by
            simp only [vm₁]
            by_cases hl' : l < p.size
            · simp [show l < p.size + 1 by lia, *]
            · simp only [Nat.not_lt] at hl'
              by_cases l = p.size
              · simp [*]
              · simp [show p.size + 1 ≤ l by lia, *]
          rw [this] at h
          exact ⟨l, hl, Or.inl ⟨hmm', by grind, h⟩⟩
      · grind
      · grind
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ h₁ hs₁ p₂ e₂' fm₂ h₂ hs₂ h ih₁ ih₂ =>
    grind [validRefs_subst, validSubst_subst, subst_wf, Expr.wfSubst_in_subst]
  next p vm fm c et ef p₁ c' fm₁ h₁ hs₁ vm₁ p₂ et' fm₂ h₂ hs₂ p₃ ef' fm₃ h₃ hs₃
      hf ihc ihet ihef =>
    grind [validRefs_subst, validSubst_subst, subst_wf, Expr.wfSubst_in_subst]
  next => grind

theorem Program.free_in_fn_of_free_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (hwf : p.WF) (hwfs : p.WFSubst vm fm) (ho : e.DeepOriginal p fm)
    (hwfe : e.WFSubst p vm fm) {n' m : Nat} (hm : m < p.size) :
    let (eq := hs) ⟨p', _, fm', _⟩ := e.subst p vm fm
    fm'.Dom m → n' ≠ fm'[m] → p'.fn[fm'[m]].Free p' n' →
      ∃ (n : Nat) (hf : p.fn[m].Free p n),
          (¬fm'.Dom n ∧ vm[n].Free p n' ∨ fm'[n] = n' ∧ fm'.Dom n) := by
  intro hfmm hne hf
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  have hp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    validSubst_subst hvm hfm hp hvalid ho
  have hwfs' : p'.WFSubst vm.extend fm' :=
    wfSubst_subst hvm hfm hp hvalid hwf ho hwfs hwfe
  obtain ⟨k', hk', hlv, hpath⟩ := (free_in_fn_iff _ hne).mp hf
  generalize hmm' : fm'[m] = m' at hpath
  induction hpath generalizing m with
  | refl m' hne =>
    have hn' : n' < p'.size := by grind
    replace hlv : p'.fn[fm'[m]].LocalVar n' := by grind
    obtain ⟨n, hn, ⟨hnn', hvmn, ⟨hlv, hlc⟩ | h⟩ | ⟨hfmn, h | ⟨hlc, hnn'⟩⟩⟩ :=
      hwfs' hfmm (by grind) hn' hlv
    · rw [prefix_subst.fn_eq hm] at hlv
      replace hn : n < p.size := hp hm hlv
      simp only [hn, VarMap.getElem_extend_lt] at hlc
      exact ⟨n, Expr.free_of_localVar hlv,
        Or.inl ⟨hnn', Expr.free_of_localVar hlc⟩⟩
    · grind
    · grind
    · rw [prefix_subst.fn_eq hm] at hlc
      replace hn : n < p.size := hp hm hlc
      exact ⟨n, Expr.free_of_localVar hlc, Or.inr ⟨hfmn, hnn'⟩⟩
  | step m' l' k' hne hs hpath ih =>
    obtain ⟨_, hlf⟩ := hs
    have hl' : l' < p'.size := by grind
    replace hlf : p'.fn[fm'[m]].LocalFn l' := by grind
    obtain ⟨l, hl, ⟨hll', hnnests, ⟨hlvm, hlf⟩ | ⟨hlf, rfl, -⟩⟩ | ⟨rfl, h | ⟨hlf, hfml⟩⟩⟩ :=
      hwfs' hfmm (by grind) hl' hlf
    · replace hl : l < p.size := by grind
      replace hlf : vm[l].LocalFn l' := by grind
      replace hl' : l' < p.size := by grind
      replace hk' : k' < p.size := by grind
      replace hpath : l' ⟶[p, n']* k' := by grind
      rw [prefix_subst.fn_eq hm] at hlvm
      rw [prefix_subst.fn_eq hk'] at hlv
      exact ⟨l, Expr.free_of_localVar hlvm,
        Or.inl ⟨hll', Expr.free_iff.mpr (Or.inr ⟨l', k', hk', hlf, hpath, hlv⟩)⟩⟩
    · replace hl' : l' < p.size := by grind
      replace hk' : k' < p.size := by grind
      have hn' : n' < p.size := by grind
      have hne := hpath.ne_start
      have hfmn : ¬fm'.Dom n' := by
        intro hfmn
        obtain ⟨n, hvmn, hnests⟩ := hvalid'.nests_of_dom hfmn
        refine hnnests n hvmn
          (.trans _ _ _ hnests (.free _ _ (by grind) (by lia) hne ?_))
        exact (free_in_fn_iff (by lia) hne).mpr ⟨_, ‹_›, hlv, hpath⟩
      replace hpath : l' ⟶[p, n']* k' := by grind
      rw [prefix_subst.fn_eq hm] at hlf
      rw [prefix_subst.fn_eq hk'] at hlv
      have hne := hpath.ne_start
      replace hf : p.fn[l'].Free p n' :=
        (free_in_fn_iff hl' hne).mpr ⟨_, hk', hlv, hpath⟩
      have hvmn' : vm[n'] = .var n' := by
        false_or_by_contra
        rename_i hvmn'
        replace hvmn' : vm.Dom n' := ⟨_, hvmn'⟩
        grind [Nests.free _ _ hn' hl' hne hf]
      exact ⟨n', free_in_fn_of_succ hl' hne ⟨hm, hlf⟩ hf,
        Or.inl ⟨hfmn, hvmn' ▸ .var⟩⟩
    · grind
    · rw [prefix_subst.fn_eq hm] at hlf
      replace hl : l < p.size := by grind
      replace hne := hpath.ne_start
      replace hf := (free_in_fn_iff hl' hne).mpr ⟨k', hk', hlv, hpath⟩
      obtain ⟨n, hf, h⟩ := ih hl hfml hne hf hk' hlv rfl
      exact ⟨n, free_in_fn_of_succ hl (by grind) ⟨hm, hlf⟩ hf, h⟩

theorem Expr.free_of_free_in_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (hwf : p.WF) (hwfs : p.WFSubst vm fm)
    (ho : e.DeepOriginal p fm) (hwfe : e.WFSubst p vm fm)
    {n' : Nat} :
    let ⟨p', e', fm', h⟩ := e.subst p vm fm
    e'.Free p' n' → ∃ (n : Nat) (hf : e.Free p n),
      (¬fm'.Dom n ∧ vm[n].Free p n' ∨ fm'[n] = n' ∧ fm'.Dom n) := by
  intro hf
  let p' := (e.subst p vm fm).program
  let e' := (e.subst p vm fm).expr
  let fm' := (e.subst p vm fm).funMap
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  have he' : e'.ValidRefs p' := validRefs_subst hvm hfm ho
  obtain hlv | ⟨m', k', hk', hlf, hpath, hlv⟩ := free_iff.mp hf
  · have hn' : n' < p'.size := by grind
    obtain ⟨n, hn, ⟨hfmn, hnnests, ⟨hlv, hl⟩ | ⟨-, -, h⟩⟩ | ⟨hfmn, h | ⟨hlv, hnn'⟩⟩⟩ :=
      strongProvenance_subst hvm hfm hp hvalid hwf ho hwfe hn' hlv
    · exact ⟨n, free_of_localVar hlv,
        Or.inl ⟨hfmn, free_of_localVar (by grind)⟩⟩
    · contradiction
    · contradiction
    · exact ⟨n, free_of_localVar hlv, Or.inr ⟨hfmn, hnn'⟩⟩
  · have hm' : m' < p'.size := by grind
    have hne := hpath.ne_start
    replace hf' := (Program.free_in_fn_iff hm' hne).mpr ⟨_, hk', hlv, hpath⟩
    obtain ⟨m, hm, ⟨hfmm, hnnests, h⟩ | ⟨rfl, h | ⟨hlf, hmm'⟩⟩⟩ :=
      strongProvenance_subst hvm hfm hp hvalid hwf ho hwfe hm' hlf
    · replace hm : m < p.size := by grind
      replace hm' : m' < p.size := by grind
      obtain ⟨hlv, hlc⟩ | ⟨hlf, rfl, -⟩ := h
      · refine ⟨m, free_of_localVar hlv, Or.inl ⟨hfmm, ?_⟩⟩
        exact free_of_localFn_of_free hm' hne (by grind) (by grind)
      · have hn' : n' < p.size := by grind
        have hfmn : ¬fm'.Dom n' := by
          intro hfmn
          obtain ⟨n, hvmn, hnests⟩ := hvalid'.nests_of_dom hfmn
          refine hnnests n hvmn
            (.trans _ _ _ hnests (.free _ _ (by grind) (by lia) hne ?_))
          exact (Program.free_in_fn_iff (by lia) hne).mpr ⟨_, ‹_›, hlv, hpath⟩
        have hvmn' : vm[n'] = .var n' := by
          false_or_by_contra
          rename_i hvmn'
          replace hvmn' : vm.Dom n' := ⟨hn', hvmn'⟩
          exact hnnests n' (by grind) (.free _ _ (by grind) (by lia) hne hf')
        exact ⟨n', free_of_localFn_of_free hm' hne hlf (by grind),
          Or.inl ⟨hfmn, hvmn' ▸ Free.var⟩⟩
    · contradiction
    · replace hm : m < p.size := by grind
      obtain ⟨n, hf, h⟩ :=
        Program.free_in_fn_of_free_in_subst hvm hfm hp hvalid hwf hwfs ho hwfe
        hm hmm' hne hf'
      exact ⟨n, free_of_localFn_of_free hm (by grind) hlf hf, h⟩

public section

theorem Computation.free_of_free_in_subst {c : Computation} {n m : Nat}
    {v : Expr} (hp : c.ValidRefs) (he : c.expr.ValidRefs c.toProgram)
    (hv : v.ValidRefs c.toProgram) (hwf : c.WF)
    (hwfe : ∀ k, c.expr.Free c.toProgram k → k ≽[c.toProgram] n)
    (hf : (c.subst n v).Free m) : c.Free m ∧ m ≠ n ∨ v.Free c.toProgram m := by
  obtain ⟨p, e⟩ := c
  dsimp only at *
  let vm := VarMap.mk p.size n v
  let fm := FunMap.mk p.size
  have hvm : vm.Valid fm := VarMap.valid_mk hv
  have hfm : fm.Valid := FunMap.valid_mk
  have hvalid : p.ValidSubst vm fm := Program.validSubst_mk hwf
  have ho := Expr.deepOriginal_mk hp he
  have hnnests : ∀ k, e.Free p k → n ⊁[p] k := by
    intro k hf hnests
    cases hwfe _ hf with
    | refl _ => exact hwf hnests
    | nests _ h => exact hwf (.trans _ _ _ hnests h)
  have hwfs : e.WFSubst p vm fm := by
    intro k l hnests hf h
    have : n ≠ k := by
      intro rfl
      exact hnnests _ hf hnests
    grind
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  obtain ⟨k, hf, ⟨hkk', hf'⟩ | ⟨hfmk, hne⟩⟩ :=
    Expr.free_of_free_in_subst hvm hfm hp hvalid hwf Program.wfSubst_mk ho hwfs hf
  · by_cases n = k
    · subst k
      simp only [VarMap.mk, Vector.getElem_setIfInBounds_self, vm] at hf'
      exact Or.inr hf'
    · simp only [VarMap.mk, ne_eq, not_false_eq_true, Vector.getElem_setIfInBounds_ne,
        Vector.getElem_ofFn, Expr.free_in_var_iff, vm, *] at hf'
      exact Or.inl ⟨hf' ▸ hf, hf' ▸ ‹n ≠ k›.symm⟩
  · have hfmk : ¬fm'.Dom k := by
      intro hfmk
      obtain ⟨l, hvml, hnests⟩ := hvalid'.nests_of_dom hfmk
      replace hnests : n ≻[p] k := by grind
      exact hnnests _ hf hnests
    contradiction

theorem Computation.subst_types {c : Computation} {t : Ty} {n : Nat} {v : Expr}
    (hn : n < c.size) (ht : ⊢ c : t) (hv : c.toProgram ⊢ v : c.ty[n]) :
    ⊢ c.subst n v : t := by
  refine ⟨Program.subst_types ht.program_types ?hvm ?hfm,
          Expr.subst_types ht.expr_types ?hvm ?hfm⟩
  · exact VarMap.mk_types hn hv
  · exact FunMap.mk_types

theorem Computation.subst_wf {c : Computation} {n : Nat} {v : Expr}
    (hp : c.ValidRefs) (he : c.expr.ValidRefs c.toProgram)
    (hv : v.ValidRefs c.toProgram) (h : c.WF) :
    (c.subst n v).WF :=
  Program.subst_wf (VarMap.valid_mk hv) FunMap.valid_mk hp
    (Program.validSubst_mk h) (Expr.deepOriginal_mk hp he) h

/--
Substitution preserves types and well-formedness.

Corresponds to Lemma 3 in the paper.
-/
theorem Computation.subst_types_and_wf {c : Computation} {n : Nat} {v : Expr}
    {t : Ty} (hn : n < c.size) (ht : ⊢ c : t) (hv : c.toProgram ⊢ v : c.ty[n])
    (hwf : c.WF) : ⊢ c.subst n v : t ∧ (c.subst n v).WF :=
  ⟨subst_types hn ht hv,
    subst_wf ht.program_types.validRefs ht.expr_types.validRefs hv.validRefs hwf⟩

end
