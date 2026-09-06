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
  if hf : ∀ n, e.Free p n → ¬vm.Dom n then
    -- The expression does not contain a free substitution variable, so there is
    -- nothing to do.
    ⟨p, e, fm, by rfl, by simp, by simp, by simp⟩
  else
    match e with
    | var m => ⟨p, vm[m], fm, by rfl, by simp, by grind, by simp⟩
    | fn m =>
      have hm : m < p.size := by grind
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
    | const c => by simp at hf
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
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' ih =>
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
    have .var _ _ := ht
    apply hvm
  next p vm fm m hm hfmm hf =>
    have .fn _ _ := ht
    obtain ⟨_, hty, hret⟩ := hfm _ ‹m < p.size›
    rw [hty, hret]
    constructor
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have .fn _ _ := ht
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst hp₂
    have hty : p.ty[m] = p₃.ty[p.size] := by grind [Program.prefix_subst.ty_eq]
    have hret : p.ret[m] = p₃.ret[p.size] := by grind [Program.prefix_subst.ret_eq]
    rw [hty, hret]
    constructor
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
  next p vm fm e i hf p' e' fm' h hs ih =>
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
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' ih =>
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
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
    rw [hs₂] at ih
    dsimp only at ih ⊢
    have hext := extends_update hm hfm (by grind) hfmm
    obtain ⟨hom, hm, ho⟩ := Expr.deepOriginal_fn_iff.mp ho
    apply extends_trans
    · exact hext
    · apply ih
      · exact valid_update hm hom hfm
      · exact Expr.deepOriginal_of_extends Program.prefix_push hext ho
  next p vm fm k e₁ e₂ hf p₁ e₁' fm₁ h₁ hs₁ p₂ e₂' fm₂ h₂ hs₂ ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    dsimp only at ih₁ ih₂ ⊢
    obtain ⟨ho₁, ho₂⟩ := Expr.deepOriginal_bin_iff.mp ho
    have hext₁ := ih₁ hfm ho₁
    have hext₂ := ih₂ hext₁.valid (Expr.deepOriginal_of_extends h₁.pre hext₁ ho₂)
    exact extends_trans hext₁ hext₂
  next p vm fm c et ef hf p₁ c' fm₁ h₁ hs₁ vm₁ p₂ et' fm₂ h₂ hs₂ p₃ ef' fm₃ h₃
      hs₃ ihc ihet ihef =>
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
  next p vm fm e i hf p' e' fm' h hs ih =>
    rw [hs] at ih
    dsimp at ih ⊢
    exact ih hfm (Expr.deepOriginal_proj_iff.mp ho)

theorem FunMap.valid_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (h : fm.Valid) (ho : e.DeepOriginal p fm) :
    (e.subst p vm fm).funMap.Valid :=
  (extends_subst h ho).valid

grind_pattern FunMap.valid_subst => (e.subst p vm fm).funMap

def Expr.PartialProvenance {n : Nat} (e e' : Expr) (fm : FunMap n) : Prop :=
  ∀ ⦃m r⦄ (hm : fm.Dom m), e'.Local fm[m] r → e.Local m r

structure VarMap.Valid {n : Nat} (vm : VarMap n) (fm : FunMap n) : Prop where
  bounded : ∀ {m} (_ : m < n), vm[m].Bounded n
  partialProvenance : ∀ {m} (hm : fm.Dom m),
    Expr.PartialProvenance (.var m) vm[m] fm
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
  case partialProvenance =>
    intro m hfmm n r hfmn hl
    have hm : m < p.size := by grind
    have hn : n < p.size := by grind
    by_cases i = m
    · grind
    · have : i ≠ n := by grind
      apply hvm.partialProvenance <;> grind
  case original => grind [Expr.original_update, hvm.original]

theorem VarMap.valid_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid)
    (ho : e.DeepOriginal p fm) :
    vm.extend.Valid (e.subst p vm fm).funMap := by
  fun_induction Expr.subst <;> try grind
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' ih =>
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
    case partialProvenance =>
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
        · apply hvm₂.partialProvenance hfmk hfml
          simp [vm₁, show k < p.size + 1 by lia, *]
      · apply hvm₂.partialProvenance hfmk hfml
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

@[grind .]
theorem Expr.partialProvenance_bin {k : BinKind} {e₁ e₁' e₂ e₂' : Expr}
    {n : Nat} {fm : FunMap n} (hf : e₁.PartialProvenance e₁' fm)
    (he : e₂.PartialProvenance e₂' fm) :
    (e₁.bin k e₂).PartialProvenance (e₁'.bin k e₂') fm := by
  grind [PartialProvenance]

@[grind .]
theorem Expr.partialProvenance_cond {c c' et et' ef ef' : Expr} {n : Nat}
    {fm : FunMap n} (hc : c.PartialProvenance c' fm)
    (het : et.PartialProvenance et' fm) (hef : ef.PartialProvenance ef' fm) :
    (c.cond et ef).PartialProvenance (c'.cond et' ef') fm := by
  grind [PartialProvenance]

@[grind .]
theorem Expr.partialProvenance_proj {e e' : Expr} {i : Fin 2} {n : Nat}
    {fm : FunMap n} (he : e.PartialProvenance e' fm) :
    (e.proj i).PartialProvenance (e'.proj i) fm := by
  grind [PartialProvenance]

@[grind ⇐]
theorem Expr.partialProvenance_of_extends {e e' : Expr} {n n' : Nat}
    {fm : FunMap n} {fm' : FunMap n'} (hext : fm'.Extends fm)
    (he : e'.Bounded n) (h : e.PartialProvenance e' fm) :
    e.PartialProvenance e' fm' := by
  intro n r hfmn hl
  replace hfmn : fm.Dom n := by grind
  exact h hfmn (hext.eq hfmn ▸ hl)

theorem Expr.partialProvenance_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (ho : e.DeepOriginal p fm) :
    let ⟨_, e', fm', _⟩ := e.subst p vm fm
    e.PartialProvenance e' fm' := by
  fun_induction Expr.subst
  next p e vm fm h =>
    intro n r hn hl
    have := (ho.1 hl).map
    contradiction
  next p vm fm m h =>
    intro n r hn hl
    have hm : m < p.size := by grind
    by_cases hfmm : fm.Dom m
    · exact hvm.partialProvenance hfmm hn hl
    · simp only [free_in_var_iff, forall_eq, Classical.not_not] at h
      grind [hvm.original h hfmm hl]
  next p vm fm m hm hfmm hf =>
    intro n r hfmn hl
    grind [hfm.inj]
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
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
  all_goals grind [validRefs_subst]

theorem Program.validRefs_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (ho : e.DeepOriginal p fm) : (e.subst p vm fm).program.ValidRefs := by
  fun_induction Expr.subst <;> try simpa using hp
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
    rw [hs₂] at ih
    dsimp only at ih ⊢
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm (by grind) hfm
    have hp₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind)) (by grind)
    have hf' : f'.ValidRefs p₂ := by grind [Expr.validRefs_subst]
    exact validRefs_setBody (by grind) hp₂ hf'
  all_goals grind

grind_pattern Program.validRefs_subst => (e.subst p vm fm).program

def Program.PartialProvenance (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃m⦄ (hm : fm.Dom m) (_ : fm[m] < p.size),
    ¬vm.Dom m → p.fn[m].PartialProvenance p.fn[fm[m]] fm

theorem Program.partialProvenance_mk {p : Program} {n : Nat} {v : Expr} :
    p.PartialProvenance (.mk _ n v) (.mk _) := by
  intro m hfmm
  grind

theorem Program.partialProvenance_push_recurse {p : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} {i : Nat} (hi : i < p.size)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hprov : p.PartialProvenance vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).PartialProvenance
      (vm.update i hi) (fm.update i hi) := by
  let p' := p.push (.recurse p.size) p.ty[i] p.ret[i]
  intro m hfmm hm' hvmm n r hfmn hl
  have him : i ≠ m := by grind
  have hin : i ≠ n := by grind
  have hm : m < p.size := by grind
  have hn : n < p.size := by grind
  rw [prefix_push.fn_eq hm]
  replace hl : p.fn[fm[m]].Local fm[n] r := by grind
  replace hfmm : fm.Dom m := by grind
  replace hfmn : fm.Dom n := by grind
  replace hvmm : ¬vm.Dom m := by grind
  exact hprov hfmm (hfm.lt hm) hvmm hfmn hl

@[grind .]
theorem Program.partialProvenance_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hprov : p.PartialProvenance vm fm)
    (ho : e.DeepOriginal p fm) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    p'.PartialProvenance vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hprov
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm (by grind) hfm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := by grind
    have hprov₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
      (partialProvenance_push_recurse hm hfm hp hprov) (by grind)
    have hprov : p.fn[m].PartialProvenance f' fm₂ := by
      grind [Expr.partialProvenance_subst]
    have hpre : p.Prefix p₃ := by grind
    intro n hfmn hn' hvmn k r hfmk hl
    have hfmm : fm₂[m] = m' := by grind
    by_cases hnm : m = n
    · subst n
      simp only [Vector.getElem_set_self, p₃, hfmm] at hl
      grind [hprov hfmk hl]
    · have hnm' : fm₂[n] ≠ m' := by
        intro heq
        rw [← heq] at hfmm
        have := hfm₂.inj (by grind) (by grind) hfmm
        contradiction
      simp only [ne_eq, not_false_eq_true, Ne.symm, Vector.getElem_set_ne, p₃, hnm'] at hl
      have hne : m' ≠ n := by grind
      simpa [p₃, *] using hprov₂ hfmn hn' (by grind) hfmk hl
  all_goals grind

abbrev VarMap.Dep (p : Program) (vm : VarMap p.size) (n : Nat) : Prop :=
  ∃ m, vm.Dom m ∧ m ≻[p] n

theorem VarMap.dep_in_prefix_iff {p p' : Program} {vm : VarMap p.size} {n : Nat}
    (hp : p.ValidRefs) (h : p.Prefix p') (hn : n < p.size) :
    vm.extend.Dep p' n ↔ vm.Dep p n := by
  grind

structure Program.ValidSubst (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) where
  eq_of_local : ∀ {m} (hm : fm.Dom m) (hm' : fm[m] < p.size),
    vm.Dom m → ∀ {k r}, p.fn[fm[m]].Local k r → k = fm[m]
  dep_of_dom : ∀ {m}, fm.Dom m → vm.Dep p m
  dom_of_dep : ∀ {m}, vm.Dep p m → vm.Dom m → fm.Dom m
  original_of_dom : ∀ {m} (hm : fm.Dom m), p.fn[m].Original fm
  compat : ∀ {m} (hm : fm.Dom m), vm.Dom m → vm[m] = .var fm[m]

theorem Program.validSubst_mk {p : Program} {n : Nat} {v : Expr} (hwf : p.WF) :
    p.ValidSubst (.mk _ n v) (.mk _) := by
  constructor <;> grind [VarMap.Dom, FunMap.Dom, WF]

theorem Program.validSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {i : Nat} (hi : i < p.size) (hfm : fm.Valid)
    (hp : p.ValidRefs) (hdep : vm.Dep p i) (ho : p.fn[i].Original fm)
    (hvalid : p.ValidSubst vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).ValidSubst
      (vm.update i hi) (fm.update i hi) := by
  grind [ValidSubst, Expr.Original, FunMap.Original]

@[grind .]
theorem Program.validSubst_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    p'.ValidSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hvalid
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
    rw [hs₂] at ih
    dsimp only at ih
    simp only [Classical.not_forall, Classical.not_not] at hf
    obtain ⟨l, hf, hvml⟩ := hf
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hvml.1 hm hne hf
    have hdep : vm.Dep p m := ⟨l, hvml, hnestsm⟩
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm (by grind) hfm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind [VarMap.valid_subst]
    have hfm₂ : fm₂.Valid := by grind
    have ⟨hm, hom⟩ := ho.2 _ (.here _ .fn)
    have hvalid₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
      (validSubst_push_recurse hm hfm hp hdep hom hvalid) (by grind)
    have hpre : p.Prefix p₃ := by grind
    constructor
    case eq_of_local =>
      intro n hfmn hn' hvmn k r hl
      by_cases m = n
      · have := hvalid.dom_of_dep hdep (by grind)
        contradiction
      · rw [Vector.getElem_set_ne (by grind) hn' (by grind)] at hl
        exact hvalid₂.eq_of_local hfmn hn' (by grind) hl
    case dep_of_dom =>
      have hnestsm₃ : l ≻[p₃] m := by grind
      intro n hfmn
      by_cases m = n
      · subst n
        grind
      · obtain ⟨k, hvmk, hnests⟩ := hvalid₂.dep_of_dom hfmn
        have hb : p₂.fn[m'] = Expr.recurse m' := by
          have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [prefix_subst.fn_eq (by lia)]
          grind
        replace hnests : k ≻[p₃] n := nests_in_setBody (by grind) (by grind) hnests
        grind
    case dom_of_dep =>
      intro k hdep hvmk
      by_cases hk : k < p.size
      · have := hvalid.dom_of_dep
          ((VarMap.dep_in_prefix_iff hp hpre hk).mp hdep) (by grind)
        grind
      · grind
    case original_of_dom => grind [hvalid₂.original_of_dom]
    case compat =>
      intro k hfmk hvmk
      have hfmm : ¬fm.Dom m := by grind
      have := hvalid₂.compat hfmk (by grind)
      by_cases m = k
      · subst k
        have := hvalid.dom_of_dep hdep (by grind)
        contradiction
      · grind
  all_goals grind

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
    (hfm : fm.Valid) (hp : p.ValidRefs) (hprov : p.PartialProvenance vm fm)
    (hvalid : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) {n' m' k' : Nat}
    (hn' : p.size ≤ n') (hm' : p.size ≤ m') (hk' : p.size ≤ k') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    n' < p'.size → m' < p'.size → k' < p'.size → m' ⟶[p', n']* k' →
      ∃ (n m k : Nat) (hn : n < p.size) (hm : m < p.size) (hk : k < p.size),
        fm'[n] = n' ∧ fm'[m] = m' ∧ fm'[k] = k' ∧ m ⟶[p, n]* k := by
  intro hnlt hmlt hklt hp'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have hprov' : p'.PartialProvenance vm.extend fm' :=
    partialProvenance_subst hvm hfm hp hprov ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    validSubst_subst hvm hfm hp hvalid ho
  induction hp' with
  | refl m' hne' =>
    obtain ⟨n, hn, hnn'⟩ := exists_of_ge_in_subst hfm ho hn' hnlt
    obtain ⟨m, hm, hmm'⟩ := exists_of_ge_in_subst hfm ho hm' hmlt
    have hne : n ≠ m := by grind
    exact ⟨n, m, m, hn, hm, hm, hnn', hmm', hmm', .refl _ hne⟩
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
    by_cases hvmm : (vm.extend (n' := p'.size)).Dom m
    · grind [hvalid'.eq_of_local]
    · have hlf := hprov' hfmm (hmm' ▸ hmlt) hvmm hfml hlf'
      rw [prefix_subst.fn_eq hm] at hlf
      exact ⟨n, m, k, hn, hm, hk, hnn', hmm', hkk', .step _ _ _ hne ⟨hm, hlf⟩ hp⟩

theorem Program.free_in_fn_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hprov : p.PartialProvenance vm fm)
    (hvalid : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) {n' m' : Nat}
    (hn' : p.size ≤ n') (hm' : p.size ≤ m') (hne' : n' ≠ m') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    ∀ (_ : m' < p'.size), p'.fn[m'].Free p' n' →
      ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
        fm'[n] = n' ∧ fm'[m] = m' ∧ p.fn[m].Free p n := by
  intro hmlt hf'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have hprov' : p'.PartialProvenance vm.extend fm' :=
    partialProvenance_subst hvm hfm hp hprov ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    validSubst_subst hvm hfm hp hvalid ho
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  obtain ⟨k', hklt, hlv', hp'⟩ := (free_in_fn_iff hmlt hne').mp hf'
  have hk' : p.size ≤ k' := by grind
  have hnlt : n' < p'.size := by grind
  obtain ⟨n, m, k, hn, hm, hk, hnn', hmm', hkk', hp⟩ :=
    pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp hprov hvalid ho hn' hm'
      hk' hnlt hmlt hklt hp'
  replace hlv' : p'.fn[fm'[k]].LocalVar fm'[n] := by grind
  have hne : n ≠ m := by grind
  have hfmk : fm'.Dom k := ⟨by lia, by grind⟩
  have hfmn : fm'.Dom n := ⟨by lia, by grind⟩
  have hvmk : ¬(vm.extend (n' := p'.size)).Dom k := by
    grind [hp.ne_end, hvalid'.eq_of_local, hfm'.inj]
  have hlv := hprov' hfmk (hkk' ▸ hklt) hvmk hfmn hlv'
  rw [prefix_subst.fn_eq hk] at hlv
  exact ⟨n, m, hn, hm, hnn', hmm', (free_in_fn_iff hm hne).mpr ⟨k, hk, hlv, hp⟩⟩

theorem Program.nests_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {m n : Nat} (hn : n < p.size)
    (hp : p.ValidRefs) (h : m ≻[(e.subst p vm fm).program] n) :
    m ≻[p] n := (nests_in_prefix_iff hn hp prefix_subst).mp h

theorem Program.nests_of_nests_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hprov : p.PartialProvenance vm fm)
    (hvalid : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) {n' m' : Nat}
    (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    n' ≻[p'] m' → ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
      fm'[n] = n' ∧ fm'[m] = m' ∧ n ≻[p] m := by
  intro hnests'
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  induction hnests' with
  | free n' m' hltn hltm hne' hf' =>
    have hm' : p.size ≤ m' := by grind
    obtain ⟨n, m, hn, hm, hfmn, hfmm, hf⟩ :=
      Program.free_in_fn_of_free_in_subst_of_ge hvm hfm hp hprov hvalid ho hn'
        hm' hne' hltm hf'
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
    (hprov : p.PartialProvenance vm fm) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) (hwf : p.WF) :
    (e.subst p vm fm).program.WF := by
  intro m hnests
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  by_cases hm : m < p.size
  · exact hwf <| nests_of_nests_in_subst_of_lt hm hp hnests
  · simp only [Nat.not_lt] at hm
    have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
    replace ⟨k, l, hk, hl, hkk', hll', hnests⟩ :=
      nests_of_nests_in_subst_of_ge hvm hfm hp hprov hvalid ho hm hnests
    have hfmk : fm'.Dom k := ⟨by grind, by grind⟩
    have hfml : fm'.Dom l := ⟨by grind, by grind⟩
    obtain rfl : k = l := hfm'.inj hfmk hfml (by simp [fm', hkk', hll'])
    exact hwf hnests

grind_pattern Program.subst_wf => p.WF, (e.subst p vm fm).program

def Expr.WFSubst (e : Expr) (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃n⦄, e.Free p n → vm.Dep p n → vm.Dom n ∧ fm.Dom n

theorem Expr.wfSubst_mk {p : Program} {e : Expr} {n : Nat} {v : Expr}
    (hwf : p.WF) (hwfe : ∀ k, e.Free p k → k ≽[p] n) :
    e.WFSubst p (.mk _ n v) (.mk _) := by
  have hnnests : ∀ k, e.Free p k → n ⊁[p] k := by
    intro k hf hnests
    cases hwfe _ hf with
    | refl _ => exact hwf hnests
    | nests _ h => exact hwf (.trans _ _ _ hnests h)
  intro l hf ⟨k, h, hnests⟩
  have : n ≠ k := by
    intro rfl
    exact hnnests _ hf hnests
  grind

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

@[grind ⇐]
theorem Expr.wfSubst_of_prefix_of_extends {p p' : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {fm' : FunMap p'.size}
    (hp : p.ValidRefs) (hpre : p.Prefix p') (hext : fm'.Extends fm)
    (he : e.ValidRefs p) (h : e.WFSubst p vm fm) :
    e.WFSubst p' vm.extend fm' := by
  grind [WFSubst]

theorem Program.wfSubst_fn_mk {p : Program} {n : Nat} {v : Expr}
    (hn : n < p.size) (hwf : p.WF) :
    p.fn[n].WFSubst p (.mk _ n v) (.mk _) := by
  intro m hf ⟨k, hvmk, hnests⟩
  obtain rfl : n = k := by grind
  exfalso
  by_cases h : m = n
  · subst m
    exact hwf hnests
  · exact hwf (nests_iff.mpr ⟨hvmk.1, _, by grind, h, hf, .nests _ hnests⟩)

theorem Program.wfSubst_fn_push {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {i : Nat} {b : Expr} {t₁ t₂ : Ty} (hi : i < p.size)
    (hp : p.ValidRefs) (hwf : p.WF) (hwfe : (Expr.fn i).WFSubst p vm fm) :
    p.fn[i].WFSubst (p.push b t₁ t₂)
      (vm.update i hi) (fm.update i hi) := by
  let p' := p.push (.recurse p.size) p.ty[i] p.ret[i]
  let vm' := vm.update i hi
  let fm' := fm.update i hi
  intro k hf ⟨n, hvmn, hnests⟩
  by_cases k = i
  · grind
  · have hn : n < p.size := by grind
    replace hfmm : fm'.Dom i := by grind
    replace hnests : n ≻[p] k := by grind
    replace hf : p.fn[i].Free p k := by grind
    replace hk : k < p.size := Expr.lt_size_of_free hp (hp hi) hf
    have hmn : i ≠ n := by
      intro rfl
      exfalso
      exact hwf (nests_iff.mpr ⟨hi, _, hk, ‹k ≠ i›, hf, .nests _ hnests⟩)
    grind [hwfe (.fn _ hi ‹k ≠ i› hf) ⟨n, by grind, hnests⟩]

theorem Expr.exists_free_subst_var {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {m : Nat} {r : RefKind} (he : e.ValidRefs p)
    (hwfs : e.WFSubst p vm fm) (hdep : vm.Dep p m) (hl : e.Local m r) :
    ∃ (k : Nat), vm.Dom k ∧ e.Free p k := by
  have hm := he hl
  cases r with
  | var =>
    have hf : e.Free p m := Expr.free_of_localVar hl
    obtain ⟨hvmm, -⟩ := hwfs hf hdep
    exact ⟨m, hvmm, hf⟩
  | fn =>
    obtain ⟨n, hvmn, hnests⟩ := hdep
    obtain ⟨_, k, hk, hne, hf, hnests⟩ := Program.nests_iff.mp hnests
    replace hf := free_of_localFn_of_free _ hne hl hf
    cases hnests with
    | refl _ => exact ⟨n, hvmn, hf⟩
    | nests _ hnests =>
      obtain ⟨hvmk, -⟩ := hwfs hf ⟨n, hvmn, hnests⟩
      exact ⟨k, hvmk, hf⟩

inductive Expr.Origin (e : Expr) (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) (n : Nat) (r : RefKind) : Prop where
  | unchanged (hl : e.Local n r) (hndep : ¬vm.Dep p n)
    (h : r = .var → ¬vm.Dom n)
  | subst m (hm : vm.Dom m) (hndep : ¬vm.Dep p m)
    (hlv : e.LocalVar m) (hl : vm[m].Local n r)
  | mapped m (hm : fm.Dom m) (hmn : fm[m] = n) (hl : e.Local m r)

def Expr.Provenance (e e' : Expr) (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃n r⦄, e'.Local n r → e.Origin p vm fm n r

@[grind .]
theorem Expr.provenance_bin {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {k : BinKind} {e₁ e₁' e₂ e₂' : Expr}
    (hf : e₁.Provenance e₁' p vm fm) (he : e₂.Provenance e₂' p vm fm) :
    (e₁.bin k e₂).Provenance (e₁'.bin k e₂') p vm fm := by
  grind [Provenance, Origin]

@[grind .]
theorem Expr.provenance_cond {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {c c' et et' ef ef' : Expr}
    (hc : c.Provenance c' p vm fm) (het : et.Provenance et' p vm fm)
    (hef : ef.Provenance ef' p vm fm) :
    (c.cond et ef).Provenance (c'.cond et' ef') p vm fm := by
  grind [Provenance, Origin]

@[grind .]
theorem Expr.provenance_proj {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {e e' : Expr} {i : Fin 2}
    (he : e.Provenance e' p vm fm) :
    (e.proj i).Provenance (e'.proj i) p vm fm := by
  grind [Provenance, Origin]

@[grind ⇐]
theorem Expr.provenance_of_prefix_of_extends {p p' : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} {fm' : FunMap p'.size}
    {e e' : Expr} (hp : p.ValidRefs) (hpre : p.Prefix p')
    (hext : fm'.Extends fm) (he : e.ValidRefs p) (h : e.Provenance e' p vm fm) :
    e.Provenance e' p' vm.extend fm' := by
  intro n r hl
  obtain ⟨hl, hnnests⟩ | ⟨k, hvmk, hlv, hl⟩ | ⟨k, hfmk, hkn, hl⟩ := h hl
  · exact .unchanged hl (by grind) (by grind)
  · exact .subst k (by grind) (by grind) hl (by grind)
  · exact .mapped k (by grind) (by grind) hl

theorem Expr.provenance_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) (hwfe : e.WFSubst p vm fm) :
    let ⟨p', e', fm', _⟩ := e.subst p vm fm
    e.Provenance e' p' vm.extend fm' := by
  fun_induction subst
  next p e vm fm h =>
    intro n r hl
    have hndep : ¬vm.Dep p n := by
      intro hdep
      obtain ⟨k, hvmk, hf⟩ :=
        exists_free_subst_var ho.validRefs hwfe hdep hl
      have := h k hf
      contradiction
    refine .unchanged hl (by grind) ?_
    cases r with
    | var => grind [h n (free_of_localVar hl)]
    | fn => simp
  next p vm fm m hvmm =>
    intro n r hl
    simp only [free_in_var_iff, forall_eq, Classical.not_not] at hvmm
    have hm := hvmm.1
    by_cases hfmm : fm.Dom m
    · obtain ⟨rfl, rfl⟩ := local_var_iff.mp (hvalid.compat hfmm hvmm ▸ hl)
      exact .mapped m hfmm rfl .var
    · refine .subst m (by grind) ?_ .var (by grind)
      rw [VarMap.extend_eq]
      exact (hfmm <| hvalid.dom_of_dep · hvmm)
  next p vm fm m hf hm hfmm =>
    intro n r hl
    simp only [local_fn_iff] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact .mapped m hfmm rfl .fn
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
    intro n r hl
    obtain ⟨rfl, rfl⟩ := local_fn_iff.mp hl
    have hext : fm₂.Extends fm₁ := by grind [FunMap.valid_update]
    exact .mapped m (by grind) (by grind) .fn
  all_goals grind

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

def Program.Provenance (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) :
    Prop :=
  ∀ ⦃m⦄ (hm : fm.Dom m) (_ : fm[m] < p.size),
    ¬vm.Dom m → p.fn[m].Provenance p.fn[fm[m]] p vm fm

theorem Program.provenance_mk {p : Program} {n : Nat} {v : Expr} :
    p.Provenance (.mk _ n v) (.mk _) := by
  grind [Provenance]

theorem Expr.partialProvenance_of_provenance {p : Program} {e e' : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hvalid : p.ValidSubst vm fm) (ho : e.Original fm)
    (h : e.Provenance e' p vm fm) : e.PartialProvenance e' fm := by
  intro m r hfmm hl
  obtain ⟨hl, hndep, h⟩ | ⟨k, hvmk, hndep, hlv, hl⟩ | ⟨k, hfmk, hkm, hl⟩ := h hl
  · grind [ho hl]
  · have hfmk : ¬fm.Dom k := fun hfmk => hndep (hvalid.dep_of_dom hfmk)
    grind [hvm.original hvmk hfmk hl]
  · exact hfm.inj hfmk hfmm hkm ▸ hl

theorem Program.partialProvenance_of_provenance {p : Program}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hvalid : p.ValidSubst vm fm) (h : p.Provenance vm fm) :
    p.PartialProvenance vm fm := by
  intro m hfmm hm' hvmm
  exact Expr.partialProvenance_of_provenance hvm hfm hvalid
    (hvalid.original_of_dom hfmm) (h hfmm hm' hvmm)

theorem Program.provenance_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {i : Nat} (hi : i < p.size) (hfm : fm.Valid)
    (hp : p.ValidRefs) (hfmi : ¬fm.Dom i) (hdep : vm.Dep p i)
    (hwfs : p.Provenance vm fm) :
    (p.push (.recurse p.size) p.ty[i] p.ret[i]).Provenance
      (vm.update i hi) (fm.update i hi) := by
  intro m hfmm hm' hvmm
  by_cases m = p.size
  · grind
  · replace hm : m < p.size := by grind
    by_cases i = m
    · intro n r hlc
      grind
    · intro n r hlc
      replace hm' : fm[m] < p.size := by grind
      replace hn : n < p.size := by grind
      obtain ⟨hl, hnnests, h⟩ | ⟨k, hvmk, hnnests, hlv, hl⟩ | ⟨k, hfmk, hkn, hl⟩ :=
        hwfs (by grind) hm' (by grind) (by simpa [*] using hlc)
      · exact .unchanged (by grind) (by grind) (by grind)
      · exact .subst k (by grind) (by grind) (by grind) (by grind)
      · exact .mapped k (by grind) (by grind) (by grind)

theorem Program.provenance_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (hwf : p.WF) (ho : e.DeepOriginal p fm)
    (hwfs : p.Provenance vm fm) (hwfe : e.WFSubst p vm fm) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    p'.Provenance vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hwfs
  next p vm fm m hf hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' ih =>
    rw [hs₂] at ih
    dsimp only at *
    simp only [Classical.not_forall, Classical.not_not] at hf
    obtain ⟨l, hf, hvml⟩ := hf
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hvml.1 hm hne hf
    have hdep : vm.Dep p m := ⟨l, hvml, hnestsm⟩
    obtain ⟨hom, hm, ho⟩ := Expr.deepOriginal_fn_iff.mp ho
    have ho' : p.fn[m].DeepOriginal p₁ fm₁ := by grind
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm hom hfm
    have hp₁ : p₁.ValidRefs := validRefs_push hp (by grind)
    have hvalid₁ : p₁.ValidSubst vm₁ fm₁ :=
      validSubst_push_recurse hm hfm hp hdep ho.1 hvalid
    have hwf₁ : p₁.WF := push_wf hp hwf
    have hwfs₁ : p₁.Provenance vm₁ fm₁ :=
      provenance_push_recurse hm hfm hp hfmm hdep hwfs
    have hwfsm : p.fn[m].WFSubst p₁ vm₁ fm₁ := wfSubst_fn_push hm hp hwf hwfe
    have hwfs₂ := ih hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ ho' hwfs₁ hwfsm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := hext₂.valid
    have hmm' : fm₂[m] = m' := by grind [hext₂.eq]
    have hfmm' : fm₂[m'] = m' := by grind
    have hpre₂ : p.Prefix p₂ := prefix_trans prefix_push h₂.pre
    have hpre₃ : p.Prefix p₃ := by grind
    intro n hfmn hn' hvmn
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
    have hfmm : fm₂.Dom m := by grind
    by_cases m = n
    · subst n
      simp only [ne_eq, show m' ≠ m by lia, not_false_eq_true, Vector.getElem_set_ne,
        Vector.getElem_set_self, p₃, hmm']
      have hf' := Expr.provenance_subst hvm₁ hfm₁ hp₁ hvalid₁ ho' hwfsm
      rw [hs₂] at hf'
      dsimp only at hf'
      rw [show p₂.fn[m] = p.fn[m] by grind]
      intro k r hlc
      obtain ⟨hlc, hnnests, h⟩ | ⟨l, hvml, hnnests, hlv, hlc⟩ | ⟨l, hfml, hlk, hlc⟩ := hf' hlc
      · exact .unchanged hlc (by grind) (by grind)
      · by_cases m = l
        · exact .mapped m hfmm (by grind) (by grind)
        · exact .subst l (by grind) (by grind) (by grind) (by grind)
      · exact .mapped l hfml hlk hlc
    · have : m' ≠ n := by grind
      have : m' ≠ fm₂[n] := by
        intro h
        have := hfm₂.inj hfmm hfmn (hmm' ▸ h)
        contradiction
      simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, p₃, *]
      intro k r hlc
      obtain ⟨hlc, hnnests, h⟩ | ⟨l, hvml, hnnests, hlv, hlc⟩ | ⟨l, hfml, hlk, hlc⟩ :=
        hwfs₂ hfmn (by lia) (by grind) hlc
      · exact .unchanged hlc (by grind) (by grind)
      · have : m ≠ l := by grind
        exact .subst l (by grind) (by grind) hlv (by grind)
      · exact .mapped l hfml hlk hlc
  all_goals grind [partialProvenance_of_provenance]

theorem Program.free_in_fn_of_free_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (hwf : p.WF) (hwfs : p.Provenance vm fm) (ho : e.DeepOriginal p fm)
    (hwfe : e.WFSubst p vm fm) {n' m : Nat} (hm : m < p.size) :
    let (eq := hs) ⟨p', _, fm', _⟩ := e.subst p vm fm
    fm'.Dom m → n' ≠ fm'[m] → p'.fn[fm'[m]].Free p' n' →
      (p.fn[m].Free p n' ∧ ¬vm.Dep p n' ∧ ¬vm.Dom n') ∨
      ∃ (n : Nat) (hf : p.fn[m].Free p n),
        n ≠ m ∧ (vm.Dom n ∧ vm[n].Free p n' ∨ fm'.Dom n ∧ fm'[n] = n') := by
  intro hfmm hne hf
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  have hp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    validSubst_subst hvm hfm hp hvalid ho
  have hwfs' : p'.Provenance vm.extend fm' :=
    provenance_subst hvm hfm hp hvalid hwf ho hwfs hwfe
  obtain ⟨k', hk', hlv, hpath⟩ := (free_in_fn_iff _ hne).mp hf
  generalize hmm' : fm'[m] = m' at hpath
  induction hpath generalizing m with
  | refl m' hne =>
    replace hlv : p'.fn[fm'[m]].LocalVar n' := by grind
    have hvmm : ¬(vm.extend (n' := p'.size)).Dom m := by
      grind [hvalid'.eq_of_local, hfm'.inj]
    obtain ⟨hlc, hnnests, h⟩ | ⟨n, hvmn, hnnests, hlv, hlc⟩ | ⟨n, hfmn, hnn', hlc⟩ :=
      hwfs' hfmm (by grind) hvmm hlv
    · rw [prefix_subst.fn_eq hm] at hlc
      exact .inl ⟨Expr.free_of_localVar hlc, by grind [hvalid'.dep_of_dom], by grind⟩
    · rw [prefix_subst.fn_eq hm] at hlv
      simp only [hp hm hlv, VarMap.getElem_extend_lt] at hlc
      have hfmn : ¬fm'.Dom n := by grind [hvalid'.dep_of_dom]
      exact .inr ⟨n, Expr.free_of_localVar hlv, by grind,
        .inl ⟨by grind, Expr.free_of_localVar hlc⟩⟩
    · rw [prefix_subst.fn_eq hm] at hlc
      exact .inr ⟨n, Expr.free_of_localVar hlc, by grind, .inr ⟨hfmn, hnn'⟩⟩
  | step m' l' k' hne hs hpath ih =>
    obtain ⟨_, hlf'⟩ := hs
    replace hlf' : p'.fn[fm'[m]].LocalFn l' := by grind
    by_cases hvmm : (vm.extend (n' := p'.size)).Dom m
    · grind [hvalid'.eq_of_local]
    · obtain ⟨hlc, hnnests, h⟩ | ⟨l, hvml, hnnests, hlvm, hlc⟩ | ⟨l, hfml, rfl, hlf⟩ :=
        hwfs' hfmm (by grind) hvmm hlf'
      · rw [prefix_subst.fn_eq hm] at hlc
        replace hl' : l' < p.size := by grind
        replace hpath : l' ⟶[p, n']* k' := by grind
        replace hk' : k' < p.size := by grind
        rw [prefix_subst.fn_eq hk'] at hlv
        have hne' := hpath.ne_start
        have hf' := (free_in_fn_iff hl' hne').mpr ⟨_, hk', hlv, hpath⟩
        have hnests := Nests.free n' _ (by grind) hl' hne' hf'
        have hf := Expr.free_iff.mpr (.inr ⟨_, _, hk', hlc, hpath, hlv⟩)
        exact .inl ⟨hf, by grind [hvalid'.dep_of_dom], by grind⟩
      · replace hl : l < p.size := by grind
        replace hlf : vm[l].LocalFn l' := by grind
        replace hl' : l' < p.size := by grind
        replace hk' : k' < p.size := by grind
        replace hpath : l' ⟶[p, n']* k' := by grind
        rw [prefix_subst.fn_eq hm] at hlvm
        rw [prefix_subst.fn_eq hk'] at hlv
        exact .inr ⟨l, Expr.free_of_localVar hlvm, by grind,
          Or.inl ⟨by grind, Expr.free_iff.mpr (Or.inr ⟨l', k', hk', hlf, hpath, hlv⟩)⟩⟩
      · have hl : l < p.size := by grind
        rw [prefix_subst.fn_eq hm] at hlf
        have hne' := hpath.ne_start
        have hf' := (free_in_fn_iff (by grind) hne').mpr ⟨_, hk', hlv, hpath⟩
        obtain ⟨hf, hndep, hvmn'⟩ | ⟨n, hf, hne, h⟩ :=
          ih (by grind) hfml hne' hf' hk' hlv rfl
        · have hne : n' ≠ l := by grind [hvalid'.dep_of_dom]
          exact .inl ⟨free_in_fn_of_succ hl hne ⟨hm, hlf⟩ hf, hndep, hvmn'⟩
        · exact .inr ⟨n, Expr.free_of_localFn_of_free hl hne hlf hf, by grind, h⟩

theorem Expr.free_of_free_in_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (hwf : p.WF) (hwfs : p.Provenance vm fm)
    (ho : e.DeepOriginal p fm) (hwfe : e.WFSubst p vm fm)
    {n' : Nat} :
    let ⟨p', e', _, _⟩ := e.subst p vm fm
    e'.Free p' n' → e.Free p n' ∧ ¬vm.Dom n' ∨
      ∃ (n : Nat) (hf : e.Free p n), vm.Dom n ∧ vm[n].Free p n' := by
  intro hf
  let p' := (e.subst p vm fm).program
  let e' := (e.subst p vm fm).expr
  let fm' := (e.subst p vm fm).funMap
  have hext : fm'.Extends fm := FunMap.extends_subst hfm ho
  have hfm' : fm'.Valid := hext.valid
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  have he' : e'.ValidRefs p' := validRefs_subst hvm hfm ho
  obtain hlv | ⟨m', k', hk', hlf, hpath, hlv⟩ := free_iff.mp hf
  · have hn' : n' < p'.size := by grind
    obtain ⟨hl, hnnests, h⟩ | ⟨n, hvmn, hnnests, hlv, hl⟩ | ⟨n, hfmn, hnn', hl⟩ :=
      provenance_subst hvm hfm hp hvalid ho hwfe hlv
    · have hfmn' : ¬fm'.Dom n' := by grind [hvalid'.dep_of_dom]
      have hvmn' : vm[n'] = .var n' := by grind [VarMap.Dom]
      exact .inl ⟨free_of_localVar hl, by grind⟩
    · exact .inr ⟨n, free_of_localVar hlv, by grind, free_of_localVar (by grind)⟩
    · refine .inr ⟨n, free_of_localVar hl, ?_⟩
      have hdep := (VarMap.dep_in_prefix_iff hp (by grind) (by grind)).mp <|
        hvalid'.dep_of_dom hfmn
      obtain ⟨hvmn, hfmn⟩ := hwfe (free_of_localVar hl) hdep
      have := hvalid.compat hfmn hvmn
      rw [hext.eq hfmn] at hnn'
      exact ⟨hvmn, this ▸ hnn' ▸ .var⟩
  · have hm' : m' < p'.size := by grind
    have hne' := hpath.ne_start
    replace hf' := (Program.free_in_fn_iff hm' hne').mpr ⟨_, hk', hlv, hpath⟩
    obtain ⟨hl, hnnests, h⟩ | ⟨m, hvmm, hnnests, hlv, hl⟩ | ⟨m, hfmm, rfl, hl⟩ :=
      provenance_subst hvm hfm hp hvalid ho hwfe hlf
    · replace hm' : m' < p.size := ho.validRefs hl
      replace hpath : m' ⟶[p, n']* k' := by grind
      replace hk' : k' < p.size := by grind
      rw [Program.prefix_subst.fn_eq hk'] at hlv
      have hn' : n' < p.size := by grind
      have hf := (Program.free_in_fn_iff hm' hne').mpr ⟨_, hk', hlv, hpath⟩
      have hnests := Program.Nests.free _ _ hn' _ hne' hf
      have hvmn' : ¬vm.Dom n' := by grind
      exact .inl ⟨free_of_localFn_of_free hm' hne' hl hf, hvmn'⟩
    · replace hm' : m' < p.size := by grind
      replace hf' : p.fn[m'].Free p n' := by grind
      have hfmm : ¬fm'.Dom m := by grind [hvalid'.dep_of_dom]
      exact .inr ⟨m, free_of_localVar hlv, by grind,
        free_of_localFn_of_free hm' hne' (by grind) hf'⟩
    · have hm := ho.validRefs hl
      obtain ⟨hf, hndep, hvmn'⟩ | ⟨n, hf, hne, ⟨hvmn, hfvm⟩ | ⟨hfmn, hnn'⟩⟩ :=
        Program.free_in_fn_of_free_in_subst hvm hfm hp hvalid hwf hwfs ho hwfe
        hm hfmm hne' hf'
      · have hne : n' ≠ m := by grind [hvalid'.dep_of_dom]
        exact .inl ⟨free_of_localFn_of_free hm hne hl hf, hvmn'⟩
      · exact .inr ⟨n, free_of_localFn_of_free hm hne hl hf, hvmn, hfvm⟩
      · have hdep := (VarMap.dep_in_prefix_iff hp (by grind) (by grind)).mp <|
          hvalid'.dep_of_dom hfmn
        have hf := free_of_localFn_of_free hm hne hl hf
        obtain ⟨hvmn, hfmn⟩ := hwfe hf hdep
        have := hvalid.compat hfmn hvmn
        rw [hext.eq hfmn] at hnn'
        exact .inr ⟨n, hf, hvmn, this ▸ hnn' ▸ .var⟩

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
  have hwfs : e.WFSubst p vm fm := Expr.wfSubst_mk hwf hwfe
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  obtain ⟨hf, hvmm⟩ | ⟨k, hf, hvmk, hfvm⟩ :=
    Expr.free_of_free_in_subst hvm hfm hp hvalid hwf Program.provenance_mk ho hwfs hf
  · by_cases hmn : m = n
    · subst m
      have : vm[n] = .var n := by grind [VarMap.Dom]
      simp only [VarMap.mk, Vector.getElem_setIfInBounds_self, vm] at this
      exact .inr (this ▸ .var)
    · exact .inl ⟨hf, hmn⟩
  · grind

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
    Program.partialProvenance_mk (Program.validSubst_mk h)
    (Expr.deepOriginal_mk hp he) h

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
