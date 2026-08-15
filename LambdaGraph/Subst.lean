module

import all LambdaGraph.SubstMaps
public import LambdaGraph.Nest

@[grind]
structure SubstProps (p p' : Program) (e e' : Expr) (vm : VarMap p.size)
    (fm : FunMap p.size) (fm' : FunMap p'.size) : Prop where
  pre : p.Prefix p'
  op : Termination.OccursProvenance p p' vm vm.extend fm fm'
  ep : Termination.ExprProvenance p p' e e' vm fm
  ext : ∀ (m : Nat) hm, fm[m]'hm ≠ m → fm'[m]'(by grind) = fm[m]

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
  if ∀ n (_ : n < p.size), e.Free p n → vm[n] = var n then
    -- The expression does not contain a free substitution variable, so there is
    -- nothing to do.
    ⟨p, e, fm, by rfl, by simp, by simp, by simp⟩
  else
    match e with
    | var m =>
      ⟨p, vm[m]?.getD (var m), fm, by rfl, by simp, by grind, by simp⟩
    | fn m =>
      if hm : m < p.size then
        if hfmm : fm[m] = m then
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
          let p₃ := p₂.setBody m' f' (hi := by grind)
          let e' := fn m'
          ⟨p₃, e', fm₂, by
            refine ⟨?_, ?_, ?_, ?_⟩
            · constructor <;> grind
            · have hop' : OccursProvenance p p₂ vm vm₁.extend fm fm₂ := by
                grind [Occurs, OccursProvenance, Program.UsesFn]
              grind [Occurs, OccursProvenance, Program.UsesFn]
            · grind [ExprProvenance]
            · grind
          ⟩
        else
          -- There is already a substitution for this function, we can reuse it.
          ⟨p, fn fm[m], fm, by rfl, by simp, by grind, by simp⟩
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
    have hm₂ : m ∈ reachableUnmapped p (fn m) fm := by grind
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
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ f'' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have .fn _ _ := ht
    have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
    subst hp₂
    have hty : p.ty[m] = p₃.ty[p.size]'(by grind) := by grind [Program.prefix_subst.ty_eq]
    have hret : p.ret[m] = p₃.ret[p.size]'(by grind) := by grind [Program.prefix_subst.ret_eq]
    rw [hty, hret]
    constructor
  next p vm fm m hm hfmm hf =>
    have .fn _ _ := ht
    obtain ⟨_, hty, hret⟩ := hfm _ ‹m < p.size›
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
    (hm : m < n) (h : fm.Original fm[m]) : fm[m] = m := h.2 hm rfl

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
  ∀ ⦃m r⦄ (_ : m < n), fm[m] ≠ m → e'.Local fm[m] r → m = k ∨ e.Local m r

structure FunMap.Valid {n : Nat} (fm : FunMap n) : Prop where
  lt : ∀ {m} (_ : m < n), fm[m] < n
  inj : ∀ {m k} (_ : m < n) (_ : k < n),
    fm[m] ≠ m → fm[k] ≠ k → fm[m] = fm[k] → m = k
  idem : ∀ {m} (_ : m < n), (fm[fm[m]]'(lt _)) = fm[m]

grind_pattern FunMap.Valid.lt =>
  fm.Valid, m < n, fm[m]
  where m =/= fm[_]'_

attribute [grind =] FunMap.Valid.idem

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
      have := hfm.2 hm
      grind

structure FunMap.Extends {n' n : Nat} (fm' : FunMap n') (fm : FunMap n) : Prop where
  valid : fm'.Valid
  le : n ≤ n'
  eq : ∀ {m} (_ : m < n), fm[m] ≠ m → fm'[m] = fm[m]
  eq_of_lt : ∀ {m} (_ : m < n'), fm'[m] < n → ∃ (_ : m < n), fm'[m] = fm[m]
  exists_of_ge : ∀ {m'}, n ≤ m' → m' < n' → ∃ (m : Nat) (_ : m < n), fm'[m] = m'

grind_pattern FunMap.Extends.eq =>
  fm'.Extends fm, fm[m], fm'[m]

theorem FunMap.extends_self {n : Nat} {fm : FunMap n} (hfm : fm.Valid) :
    fm.Extends fm := by constructor <;> grind

@[grind →]
theorem FunMap.extends_trans {n₀ n₁ n₂ : Nat} {fm₀ : FunMap n₀}
    {fm₁ : FunMap n₁} {fm₂ : FunMap n₂} (h : fm₁.Extends fm₀)
    (h' : fm₂.Extends fm₁) : fm₂.Extends fm₀ := by
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
      exact ⟨m, hm, by grind⟩
    · simp only [Nat.not_lt] at h
      obtain ⟨m, hm, hfmm⟩ := h₂' h hlt
      by_cases h : m < n₀
      · exact ⟨m, h, hfmm⟩
      · simp only [Nat.not_lt] at h
        obtain ⟨k, hk, hfmk⟩ := h₂ h hm
        have heq := h₀' (show k < n₁ by lia) (by grind)
        have := hfm₂.idem (show k < n₂ by lia)
        simp [heq, hfmk] at this
        grind
  · grind

theorem FunMap.extends_update {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n)
    (hfm : fm.Valid) (h : fm.Original m) (hfmm : fm[m] = m) :
    (fm.update m hm).Extends fm := by
  constructor <;> grind [valid_update]

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
  localProvenance : ∀ {m} (_ : m < n),
    fm[m] ≠ m → fm.LocalProvenance (.var m) vm[m] none
  original : ∀ {m} (_ : m < n),
    fm[m] = m → vm[m] ≠ .var m → vm[m].Original fm

attribute [grind! .] VarMap.Valid.bounded

theorem VarMap.valid_mk {n m : Nat} {v : Expr} (hv : v.Bounded n) :
    (mk n m v).Valid (.mk n) := by
  constructor <;> grind [Expr.original_mk]

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
  case original =>
    intro m hm hmm' hne
    grind [Expr.original_update, hvm.original]

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
      intro k hk hkk' l r hl hll' hlc
      by_cases k < p.size
      · simp only [VarMap.getElem_extend_lt, *] at hlc
        by_cases m = k
        · subst k
          have hl' : fm₂[l] < p.size := hvm.bounded hm hlc
          obtain ⟨hl, heq⟩ := hext.eq_of_lt hl hl'
          rw [heq] at hlc
          by_cases hvmm : vm[m] = .var m
          · grind
          · grind [hvm.original hm (by simp [*]) hvmm hlc]
        · exact hvm₂.localProvenance hk hkk' hl hll' (by grind)
      · exact hvm₂.localProvenance hk hkk' hl hll' (by grind)
    case original =>
      intro k hk hkk' hne
      dsimp only at hk hkk'
      by_cases hk : k < p.size
      · have hkk' : fm[k] = k := by grind
        simp only [getElem_extend_lt, *] at hne ⊢
        exact Expr.original_of_extends hext (hvm.original hk hkk' hne)
      · simp_all

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
    intro n r hn hnn' hl
    have := (ho.1 hl).map
    contradiction
  next p vm fm m h =>
    intro n r hn hnn' hl
    have hm : m < p.size := by grind
    simp only [hm, getElem?_pos, Option.getD_some] at hl
    by_cases hmm' : fm[m] = m
    · simp only [Classical.not_forall] at h
      obtain ⟨k, hk, hf, hne⟩ := h
      have .var := hf
      have := hvm.original hm hmm' hne hl
      grind
    · exact hvm.localProvenance hm hmm' hn hnn' hl
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih ⊢
    have hext₁ : fm₁.Extends fm := by grind
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm (by grind) hfm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := hext₂.valid
    intro n r hn hnn' hl
    subst e'
    simp only [local_fn_iff] at hl
    obtain ⟨hr, hmn'⟩ := hl
    have : fm₂[m]'(by grind) = m' := by grind
    rw [← this] at hmn'
    have : m = n := hfm₂.inj (by grind) hn (by grind) hnn' hmn'
    simp [*]
  next p vm fm m hm hfmm hf =>
    intro n r hn hnn' hl
    grind [hfm.inj]
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
    intro n r hn hnn' hl
    have hext₁ : fm₃.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    have hvc' : c'.ValidRefs p₁ := by grind [validRefs_subst]
    have hvet' : et'.ValidRefs p₂ := by
      grind [validRefs_subst]
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
  next p vm fm e i p' e' fm' h hs hf ih =>
    rw [hs] at ih
    dsimp only at ih ⊢
    intro n r hn hnn' hl
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
  fn_localProvenance : ∀ {m m'} (_ : m < p.size) (_ : m' < p.size),
    m' = fm[m] → m' ≠ m → fm.LocalProvenance p.fn[m] p.fn[m'] m
  eq_of_not_nests : ∀ {m} (_ : m < p.size),
    (∀ n (_ : n < p.size), vm[n] ≠ .var n → n ⊁[p] m) → fm[m] = m
  new_subst_var : ∀ {n m} (_ : n < p.size) (_ : m < p.size),
    vm[n] ≠ .var n → n ≻[p] m → fm[m] = m → vm[m] = .var m
  compat : ∀ {m} (_ : m < p.size), -- TODO Move to VarMap instead of localProvenance?
    fm[m] ≠ m → vm[m] = .var m ∨ vm[m] = .var fm[m]

theorem Program.validSubst_mk {p : Program} {n : Nat} {v : Expr} (hwf : p.WF) :
    p.ValidSubst (.mk _ n v) (.mk _) := by
  constructor <;> grind [WF]

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
      · simp only [FunMap.getElem_update_eq, *] at hfmm
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
    (hvalid : p.ValidSubst vm fm) (ho : e.DeepOriginal p fm) :
    let ⟨p', _, fm', _⟩ := e.subst p vm fm
    p'.ValidSubst vm.extend fm' := by
  fun_induction Expr.subst <;> try simpa using hvalid
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    rw [hs₂] at ih
    dsimp only at ih
    simp only [Classical.not_forall] at hf
    obtain ⟨l, hl, hf, hvml⟩ := hf
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hl hm hne hf
    have hext₁ : fm₁.Extends fm := FunMap.extends_update hm hfm (by grind) hfmm
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := hext₁.valid
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hvm₂ : vm₁.extend.Valid fm₂ := by grind [VarMap.valid_subst]
    have hfm₂ : fm₂.Valid := by grind
    have hvalid₂ := ih hvm₁ hfm₁ (validRefs_push hp (by grind))
      (validSubst_push_recurse hl hm hfm hp hvml hnestsm hvalid) (by grind)
    have hvmm : vm[m] = .var m :=
      hvalid.new_subst_var hl hm hvml hnestsm (by simp [hfmm])
    have hext := FunMap.extends_trans hext₁ hext₂
    have hprov : fm₂.LocalProvenance p.fn[m] f' none := by
      grind [Expr.localProvenance_subst, ⇐ Expr.bounded_of_ge]
    have hp₃ : p₃ = ((Expr.fn m).subst p vm fm).program := by
      grind [Expr.subst]
    have hpre : p.Prefix p₃ := hp₃ ▸ prefix_subst
    constructor
    case fn_localProvenance =>
      intro n n' hn hn' hfmn hnn' k r hk hkk' hl
      subst n'
      have hfmm : fm₂[m]'(by grind) = m' := by grind [hext₂.eq]
      by_cases hnm : m = n
      · subst n
        simp only [Vector.getElem_set_self, p₃, hfmm] at hl
        replace hl := hprov hk hkk' hl
        simp only [reduceCtorEq, false_or] at hl
        rw [hfmm] at hnn'
        have heq : p₂.fn[m] = p.fn[m] := by
          have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [prefix_subst.fn_eq (by lia)]
          simp [p₁, hm]
        simp [p₃, *]
      · have hnm' : fm₂[n] ≠ m' := by
          intro heq
          rw [← heq] at hfmm
          have := hfm₂.inj (by lia) hn (by lia) (by grind) hfmm
          contradiction
        simp only [ne_eq, not_false_eq_true, Ne.symm, Vector.getElem_set_ne, p₃, hnm'] at hl
        have hne : m' ≠ n := by grind
        cases hvalid₂.fn_localProvenance hn hn' rfl hnn' hk hkk' hl <;> simp [p₃, *]
    case eq_of_not_nests =>
      have hnestsm₃ : l ≻[p₃] m := by grind
      intro n hn h
      by_cases m = n
      · subst n
        exfalso
        exact h l (by grind) (by simpa [hl] using hvml) hnestsm₃
      · apply hvalid₂.eq_of_not_nests
        intro k hk hne hnests
        have hb : p₂.fn[m']'(by grind) = Expr.recurse m' := by -- TODO Remove?
          have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [prefix_subst.fn_eq (by lia)]
          grind
        replace hnests : k ≻[p₃] n := nests_in_setBody (by grind) (by grind) hnests
        grind
    case new_subst_var =>
      intro n k hn hk hvmn hnests hfmk
      by_cases hk : k < p.size
      · replace hfmk : fm[k] = k := by grind
        replace hnests : n ≻[p] k := by grind
        have hvmk := hvalid.new_subst_var (by grind) ‹_› (by grind) hnests hfmk
        grind
      · simp only [Nat.not_lt] at hk
        simp [*]
    case compat =>
      intro k hk hkk'
      cases hvalid₂.compat hk hkk' -- TODO Simplify?
      · by_cases hk : k < p₁.size
        · grind
        · grind
      · grind
  next => grind [validRefs_subst]
  next => grind [validRefs_subst]
  next => grind [validRefs_subst]

theorem Program.exists_of_ge_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hfm : fm.Valid)
    (ho : e.DeepOriginal p fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', h⟩ := e.subst p vm fm
    let hsize := h.pre.size_le
    n' < p'.size → ∃ (n : Nat) (_ : n < p.size), fm'[n] = n' := by
  intro hlt
  have hext : (e.subst p vm fm).funMap.Extends fm := FunMap.extends_subst hfm ho
  obtain ⟨n, hn, hfmn⟩ := hext.exists_of_ge hn' hlt
  grind

theorem Program.pathWithout_of_pathWithout_in_subst_of_ge {p : Program}
    {e : Expr} {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) {n' m' k' : Nat} (hn' : p.size ≤ n')
    (hm' : p.size ≤ m') (hk' : p.size ≤ k') :
    let ⟨p', _, fm', h⟩ := e.subst p vm fm
    let hsize := h.pre.size_le
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
    obtain ⟨m, hm, hfmm⟩ := exists_of_ge_in_subst hfm ho hm' hmlt
    have hl' : p.size ≤ l' := by grind
    obtain ⟨_, hlf'⟩ := hs'
    have hllt : l' < p'.size := by grind
    have ⟨n, l, k, hn, hl, hk, hfmn, hfml, hfmk, hp⟩ := ih hl' hk' hllt hklt
    have hne : n ≠ m := by grind
    have hlf := h'.fn_localProvenance
      (show m < p'.size by lia) hmlt (by lia) (by grind)
      (show l < p'.size by lia) (by lia) (by simpa [← hfml] using hlf')
    simp only [Option.some.injEq, prefix_subst.fn_eq hm, p'] at hlf
    obtain heq | hlf := hlf
    · grind
    · exact ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, .step _ _ _ hne ⟨hm, hlf⟩ hp⟩

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
  obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
    pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp hvalid ho hn' hm' hk' hnlt hmlt hklt hp'
  have hne : n ≠ m := by grind
  have hlv := h'.fn_localProvenance
    (show k < p'.size by lia) hklt (by lia) (by grind)
    (show n < p'.size by lia) (by lia) (by simpa [← hfmn] using hlv')
  rw [prefix_subst.fn_eq hk] at hlv
  simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
  exact ⟨n, m, hn, hm, hfmn, hfmm, (free_in_fn_iff hm hne).mpr ⟨k, hk, hlv, hp⟩⟩

theorem Expr.free_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hvm : vm.Valid fm)
    (hfm : fm.Valid) (hp : p.ValidRefs) (hvalid : p.ValidSubst vm fm)
    (ho : e.DeepOriginal p fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', e', fm', h⟩ := e.subst p vm fm
    let hsize := h.pre.size_le
    e'.Free p' n' → ∃ (n : Nat) (_ : n < p.size),
      fm'[n] = n' ∧ e.Free p n := by
  intro hf
  let p' := (e.subst p vm fm).program
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
    simpa using localProvenance_subst hvm hfm ho (by lia) (by lia) (heq ▸ hlv')
  · by_cases hm' : m' < p.size
    · have hk' : k' < p.size := by grind
      grind [Program.prefix_subst.fn_eq]
    · simp only [Nat.not_lt] at hm'
      have hk' : p.size ≤ k' := by grind [Program.prefix_subst.fn_eq]
      obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
        Program.pathWithout_of_pathWithout_in_subst_of_ge hvm hfm hp hvalid ho hn' hm' hk'
          ‹_› (validRefs_subst hvm hfm ho hlf') ‹_› hp'
      have hlf := localProvenance_subst hvm hfm ho
        (show m < p'.size by lia) (by lia) (by simpa [← hfmm] using hlf')
      simp only [reduceCtorEq, false_or] at hlf
      have hlv := h'.fn_localProvenance
        (show k < p'.size by lia) (show k' < p'.size by grind) (by lia) (by grind)
        (show n < p'.size by lia) (by lia) (by simpa [← hfmn] using hlv')
      rw [Program.prefix_subst.fn_eq hk] at hlv
      simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
      exact ⟨n, hn, hfmn, free_iff.mpr <| Or.inr ⟨m, k, hk, hlf, hp, hlv⟩⟩

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
      fm'[n]'(by grind) = n' ∧ fm'[m]'(by grind) = m' ∧ n ≻[p] m := by
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
    obtain ⟨n, k, hn, hk, hfmn, hfmk, hnests₁⟩ := ih₁ hn'
    obtain ⟨l, m, hl, hm, hfml, hfmm, hnests₂⟩ := ih₂ hk'
    obtain rfl : k = l :=
      hfm'.inj (by grind) (by grind) (by lia) (by lia) (by simp [fm', hfmk, hfml])
    exact ⟨n, m, hn, hm, hfmn, hfmm, .trans _ _ _ hnests₁ hnests₂⟩

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
    replace ⟨k, l, hk, hl, hfmk, hfml, hnests⟩ :=
      nests_of_nests_in_subst_of_ge hvm hfm hp h ho hm hnests
    obtain rfl : k = l :=
      hfm'.inj (by grind) (by grind) (by lia) (by lia) (by simp [fm', hfmk, hfml])
    exact hwf hnests

def Expr.WFSubst (e : Expr) (p : Program) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃n m⦄ (_ : n < p.size) (_ : m < p.size),
    n ≻[p] m → e.Free p m → vm[n] ≠ var n → vm[m] ≠ var m ∧ fm[m] ≠ m

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
    {fm : FunMap p.size} (hfm : fm.Valid) (hp : p.ValidRefs)
    (he₁ : e₁.ValidRefs p) (ho : e₂.DeepOriginal p fm)
    (h : e₁.WFSubst p vm fm) :
    let ⟨p', _, fm', _⟩ := e₂.subst p vm fm
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
    (hfm : fm.Valid) (hp : p.ValidRefs) (ho : e.DeepOriginal p fm)
    (hwfs : e.WFSubst p vm fm) (hn : n < p.size) (hvmn : vm[n] ≠ .var n)
    (hl : e.Local m r) (hnests : n ≻[p] m) :
    let ⟨_, _, fm', _⟩ := e.subst p vm fm
    (fm'[m]'(by grind)) ≠ m := by
  have hm : m < p.size := ho.validRefs hl
  fun_induction Expr.subst
  next p e vm fm h =>
    obtain ⟨k, hk, hvmk, hf⟩ :=
      Expr.exists_free_subst_var ho.validRefs hwfs hn hvmn hnests hl
    have := h k hk hf
    contradiction
  next p vm fm m h =>
    obtain ⟨rfl, rfl⟩ := Expr.local_var_iff.mp hl
    obtain ⟨-, hmm'⟩ := hwfs _ hm hnests .var hvmn
    exact hmm'
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    obtain ⟨rfl, rfl⟩ := Expr.local_fn_iff.mp hl
    have hext : fm₂.Extends fm₁ := by grind [valid_update]
    grind
  next p vm fm m hm hfmm hf =>
    dsimp only
    obtain ⟨rfl, rfl⟩ := Expr.local_fn_iff.mp hl
    assumption
  next => grind
  next => grind
  next p vm fm k e₁ e₂ p₁ e₁' fm₁ h₁ hs₁ p₂ e₂' fm₂ h₂ hs₂ h ih₁ ih₂ =>
    rw [hs₁] at ih₁
    rw [hs₂] at ih₂
    dsimp only at *
    have hext : fm₂.Extends fm₁ := by grind
    grind [Program.validRefs_subst, Expr.wfSubst_in_subst]
  next p vm fm c et ef p₁ c' fm₁ h₁ hs₁ vm₁ p₂ et' fm₂ h₂ hs₂ p₃ ef' fm₃ h₃ hs₃
      hf ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    have hext₁ : fm₂.Extends fm₁ := by grind
    have hext₂ : fm₃.Extends fm₂ := by grind
    grind [Program.validRefs_subst, Expr.wfSubst_in_subst]
  next p vm fm e i p' e' fm' h hs hf ih =>
    rw [hs] at ih
    grind

def FunMap.StrongProvenance (p : Program) (fm : FunMap p.size)
    (vm : VarMap p.size) (e e' : Expr) (k : Option Nat) : Prop :=
  ∀ ⦃m' r⦄ (_ : m' < p.size),
    e'.Local m' r →
      ∃ (m : Nat) (_ : m < p.size),
        fm[m] = m ∧ (∀ k (_ : k < p.size), vm[k] ≠ .var k → k ⊁[p] m) ∧
          (e.LocalVar m ∧ vm[m].Local m' r ∨ e.LocalFn m ∧ m' = m ∧ r = .fn) ∨
          fm[m] = m' ∧ (m = k ∨ e.Local m r ∧ m' ≠ m)

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
    have hnnests : ∀ m (_ : m < p.size), vm[m] ≠ var m → m ⊁[p] n := by
      intro m hm hvmm hnests
      obtain ⟨k, hk, hvmk, hf⟩ :=
        exists_free_subst_var ho.validRefs hwfe hm hvmm hnests hl
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
      by_cases hkk' : fm[k] = k
      · refine ⟨k, hk, Or.inl ⟨hkk', ?_, Or.inl ⟨.var, by grind⟩⟩⟩
        intro l hl hvml hnests
        exact hvmk <| hvalid.new_subst_var hl hk (by grind) hnests hkk'
      · refine ⟨k, hk, Or.inr ?_⟩
        cases hvalid.compat hk hkk' <;> grind
    · simp_all
  next p vm fm m hm hfmm m' vm₁ fm₁ p₁ p₂ f' fm₂ h₂ hs₂ p₃ e' hf ih =>
    intro m'' r hm' hl
    simp only [Expr.local_fn_iff, e'] at hl
    obtain ⟨hr, rfl⟩ := hl
    have hext : fm₂.Extends fm₁ := by grind [FunMap.valid_update]
    exact ⟨m, by lia, Or.inr (by grind [hext.eq])⟩
  next p vm fm m hm hfmm hf =>
    intro n r hn hl
    simp only [local_fn_iff] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨m, hm, Or.inr ⟨rfl, Or.inr ⟨.fn, hfmm⟩⟩⟩
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
      obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := he₁' hn hl
      · refine ⟨m, by grind, Or.inl
          ⟨hvalid₂.eq_of_not_nests (by grind) ?hf, ?hf, by grind⟩⟩
        grind
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
      obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := hc' hn hl
      · refine ⟨m, by grind, Or.inl
          ⟨hvalid₃.eq_of_not_nests (by grind) ?hc, ?hc, by grind⟩⟩
        grind
      · contradiction
      · exact ⟨m, by grind, Or.inr ⟨by grind, Or.inr ⟨hl, by grind⟩⟩⟩
    replace het' : fm₃.StrongProvenance p₃ vm.extend et et' none := by
      intro n r hn hl
      replace hn : n < p₂.size := by grind [validRefs_subst]
      obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hl, hor⟩⟩⟩ := het' hn hl
      · refine ⟨m, by grind, Or.inl
          ⟨hvalid₃.eq_of_not_nests (by grind) ?het, ?het, by grind⟩⟩
        grind
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
  ∀ ⦃m m'⦄ (_ : m < p.size) (_ : m' < p.size),
    fm[m] = m' → m' ≠ m → fm.StrongProvenance p vm p.fn[m] p.fn[m'] m

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
    (hfmi : fm[i] = i) (hnestsi : l ≻[p] i)
    (hwfs : p.WFSubst vm fm) :
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
      replace hm' : fm[m] < p.size := by grind
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

set_option maxHeartbeats 1000000 in
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
    simp only [Classical.not_forall] at hf
    obtain ⟨l, hl, hf, hvml⟩ := hf
    have hnestsm : l ≻[p] m := by
      replace .fn _ hm hne hf := hf
      exact .free _ _ hl hm hne hf
    obtain ⟨hom, hm, ho⟩ := Expr.deepOriginal_fn_iff.mp ho
    have ho' : p.fn[m].DeepOriginal p₁ fm₁ := by grind
    have hvm₁ : vm₁.Valid fm₁ := VarMap.valid_update hm hvm hfm
    have hfm₁ : fm₁.Valid := FunMap.valid_update hm hom hfm
    have hp₁ : p₁.ValidRefs := validRefs_push hp (by grind)
    have hvalid₁ : p₁.ValidSubst vm₁ fm₁ :=
      validSubst_push_recurse hl hm hfm hp hvml hnestsm hvalid
    have hwf₁ : p₁.WF := push_wf hp hwf
    have hwfs₁ : p₁.WFSubst vm₁ fm₁ :=
      wfSubst_push_recurse hfm hp hl hm hvml hfmm hnestsm hwfs
    have hwfsm : p.fn[m].WFSubst p₁ vm₁ fm₁ := by
      intro n k hn hk hnests hf hne
      by_cases m = k
      · simp only [VarMap.getElem_update_eq, ne_eq, Expr.var.injEq, FunMap.getElem_update_eq,
          and_self, vm₁, fm₁, *]
        lia
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
        simp only [ne_eq, not_false_eq_true, VarMap.getElem_update_ne, hn, hmn] at hne
        have := hwfe hn hk hnests (.fn _ hm ‹m ≠ k›.symm hf) hne
        simp [fm₁, *]
    have hwfs₂ := ih hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ ho' hwfs₁ hwfsm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hfm₂ : fm₂.Valid := hext₂.valid
    have hfmm : fm₂[m]'(by grind) = m' := by grind [hext₂.eq]
    have hfmm' : fm₂[m']'(by grind) = m' := by grind
    have hp₃ : p₃ = ((Expr.fn m).subst p vm fm).program := by
      grind [Expr.subst]
    have hpre₂ : p.Prefix p₂ := prefix_trans prefix_push h₂.pre
    have hpre₃ : p.Prefix p₃ := hp₃ ▸ prefix_subst
    intro n n' hn hn' rfl hnn'
    replace hn : n < p.size := by
      false_or_by_contra
      have hn' : p₁.size ≤ n := by grind
      obtain ⟨k, hk, hfmk⟩ :=
        exists_of_ge_in_subst (e := p.fn[m]) (vm := vm₁) hfm₁ ho' hn' (by lia)
      have hp₂ : p₂ = (p.fn[m].subst p₁ vm₁ fm₁).program := by grind
      subst p₂
      grind [hfm₂.idem]
    by_cases m = n
    · subst n
      simp only [ne_eq, show m' ≠ m by lia, not_false_eq_true, Vector.getElem_set_ne,
        Vector.getElem_set_self, p₃, hfmm]
      have hf' := Expr.strongProvenance_subst hvm₁ hfm₁ hp₁ hvalid₁ hwf₁ ho' hwfsm
      rw [hs₂] at hf'
      dsimp only at hf'
      rw [show p₂.fn[m] = p.fn[m] by grind]
      intro k r hk hlc
      obtain ⟨l, hl', ⟨hll', hnnests, h⟩ | ⟨hfml, h | ⟨hlc, h⟩⟩⟩ := hf' hk hlc
      · have hl : l < p.size := by grind
        by_cases m = l
        · exact ⟨m, by lia, Or.inr (by grind)⟩
        · exact ⟨l, hl', Or.inl ⟨hll', by
            intro k hk hvmk
            simp only [p₃] at hpre₃
            simp [nests_in_prefix_iff hl hp hpre₂] at hnnests
            rw [nests_in_prefix_iff hl hp hpre₃]
            exact hnnests k hk (by grind),
            by grind⟩⟩
      · contradiction
      · exact ⟨l, hl', Or.inr ⟨hfml, Or.inr ⟨hlc, h⟩⟩⟩
    · have : m' ≠ n := by grind
      have : m' ≠ fm₂[n] := by
        intro h
        have := hfm₂.inj (show m < p₂.size by lia) (by lia) (by lia) hnn' (hfmm ▸ h)
        contradiction
      simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, p₃, *]
      intro k r hk hlc
      obtain ⟨l, hl, ⟨hmm', hnnests, h⟩ | ⟨hfml, h | ⟨hlc, h⟩⟩⟩ :=
        hwfs₂ (by lia) (by lia) rfl hnn' hk hlc
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
          refine ⟨l, hl, Or.inl ⟨hmm', ?_, h⟩⟩
          rw [show p₂.fn[n] = p.fn[n] by grind] at h
          replace hl : l < p.size := by grind
          intro o ho hvmo hnests
          replace hnests : o ≻[p₂] l := by grind
          exact hnnests o ho (by grind) hnests
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
    (hwfe : e.WFSubst p vm fm) {n' m m' : Nat} (hm : m < p.size) :
    let ⟨p', _, fm', h⟩ := e.subst p vm fm
    let hsize := h.pre.size_le
    ∀ (_ : m' < p'.size), fm'[m] = m' → m' ≠ m → n' ≠ m' → p'.fn[m'].Free p' n' →
      ∃ (n : Nat) (hn : n < p.size), p.fn[m].Free p n ∧
          (fm'[n] = n ∧ vm[n].Free p n' ∨ fm'[n] = n' ∧ n' ≠ n) := by
  intro hm' hfmm hmm' hne hf
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  let hsize := (e.subst p vm fm).props.pre.size_le
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  have hp' : p'.ValidRefs := validRefs_subst hvm hfm hp ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    validSubst_subst hvm hfm hp hvalid ho
  have hwfs' : p'.WFSubst vm.extend fm' :=
    wfSubst_subst hvm hfm hp hvalid hwf ho hwfs hwfe
  obtain ⟨k', hk', hlv, hpath⟩ := (free_in_fn_iff _ hne).mp hf
  induction hpath generalizing m with
  | refl m' hne =>
    have hn' : n' < p'.size := by grind
    obtain ⟨n, hn, ⟨hnn', hvmn, ⟨hlv, hlc⟩ | h⟩ | ⟨hfmn, h | ⟨hlc, hnn'⟩⟩⟩ :=
      hwfs' (by lia) hm' hfmm hmm' hn' hlv
    · rw [prefix_subst.fn_eq hm] at hlv
      replace hn : n < p.size := hp hm hlv
      simp only [hn, VarMap.getElem_extend_lt] at hlc
      exact ⟨n, hn, Expr.free_of_localVar hlv,
        Or.inl ⟨hnn', Expr.free_of_localVar hlc⟩⟩
    · grind
    · grind
    · rw [prefix_subst.fn_eq hm] at hlc
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
      replace hk' : k' < p.size := by grind
      replace hpath : l' ⟶[p, n']* k' := by grind
      rw [prefix_subst.fn_eq hm] at hlvm
      rw [prefix_subst.fn_eq hk'] at hlv
      exact ⟨l, hl, Expr.free_of_localVar hlvm,
        Or.inl ⟨hll', Expr.free_iff.mpr (Or.inr ⟨l', k', hk', hlf, hpath, hlv⟩)⟩⟩
    · replace hl' : l' < p.size := by grind
      replace hk' : k' < p.size := by grind
      have hn' : n' < p.size := by grind
      have hne := hpath.ne_start
      have hnn' : fm'[n'] = n' := by
        apply hvalid'.eq_of_not_nests
        intro n hn hvmn hnests
        refine hnnests n hn hvmn
          (.trans _ _ _ hnests (.free _ _ (by lia) (by lia) hne ?_))
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
        grind [Nests.free]
      exact ⟨n', hn', free_in_fn_of_succ hl' hne ⟨hm, hlf⟩ hf,
        Or.inl ⟨hnn', hvmn' ▸ .var⟩⟩
    · grind
    · rw [prefix_subst.fn_eq hm] at hlf
      replace hl : l < p.size := by grind
      replace hne := hpath.ne_start
      replace hf := (free_in_fn_iff hl' hne).mpr ⟨k', hk', hlv, hpath⟩
      obtain ⟨n, hn, hf, h⟩ := ih hl hl' hfml hll' hne hf hk' hlv
      exact ⟨n, hn, free_in_fn_of_succ hl (by grind) ⟨hm, hlf⟩ hf, h⟩

theorem Expr.free_of_free_in_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvm : vm.Valid fm) (hfm : fm.Valid) (hp : p.ValidRefs)
    (hvalid : p.ValidSubst vm fm) (hwf : p.WF) (hwfs : p.WFSubst vm fm)
    (ho : e.DeepOriginal p fm) (hwfe : e.WFSubst p vm fm)
    {n' : Nat} :
    let ⟨p', e', fm', h⟩ := e.subst p vm fm
    let hsize := h.pre.size_le
    e'.Free p' n' → ∃ (n : Nat) (hn : n < p.size), e.Free p n ∧
      (fm'[n] = n ∧ vm[n].Free p n' ∨ fm'[n] = n' ∧ n' ≠ n) := by
  intro hf
  let p' := (e.subst p vm fm).program
  let e' := (e.subst p vm fm).expr
  let fm' := (e.subst p vm fm).funMap
  let hsize := (e.subst p vm fm).props.pre.size_le
  have hfm' : fm'.Valid := FunMap.valid_subst hfm ho
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  have he' : e'.ValidRefs p' := validRefs_subst hvm hfm ho
  obtain hlv | ⟨m', k', hk', hlf, hpath, hlv⟩ := free_iff.mp hf
  · have hn' : n' < p'.size := by grind
    obtain ⟨n, hn, ⟨hnn', hnnests, ⟨hlv, hl⟩ | ⟨-, -, h⟩⟩ | ⟨hfmn, h | ⟨hlv, hnn'⟩⟩⟩ :=
      strongProvenance_subst hvm hfm hp hvalid hwf ho hwfe hn' hlv
    · exact ⟨n, ho.validRefs hlv, free_of_localVar hlv,
        Or.inl ⟨hnn', free_of_localVar (by grind)⟩⟩
    · contradiction
    · contradiction
    · exact ⟨n, ho.validRefs hlv, free_of_localVar hlv, Or.inr ⟨hfmn, hnn'⟩⟩
  · have hm' : m' < p'.size := by grind
    have hne := hpath.ne_start
    replace hf' := (Program.free_in_fn_iff hm' hne).mpr ⟨_, hk', hlv, hpath⟩
    obtain ⟨m, hm, ⟨hmm', hnnests, h⟩ | ⟨hfmm, h | ⟨hlf, hmm'⟩⟩⟩ :=
      strongProvenance_subst hvm hfm hp hvalid hwf ho hwfe hm' hlf
    · replace hm : m < p.size := by grind
      replace hm' : m' < p.size := by grind
      obtain ⟨hlv, hlc⟩ | ⟨hlf, rfl, -⟩ := h
      · refine ⟨m, hm, free_of_localVar hlv, Or.inl ⟨hmm', ?_⟩⟩
        exact free_of_localFn_of_free hm' hne (by grind) (by grind)
      · have hn' : n' < p.size := by grind
        have hnn' : fm'[n'] = n' := by
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
        Program.free_in_fn_of_free_in_subst hvm hfm hp hvalid hwf hwfs ho hwfe
        hm hm' hfmm hmm' hne hf'
      exact ⟨n, hn, free_of_localFn_of_free hm (by grind) hlf hf, h⟩

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
    intro k l hk hl hnests hf h
    have : n ≠ k := by
      intro rfl
      exact hnnests _ hf hnests
    simp [VarMap.mk, vm, *] at h
  let p' := (e.subst p vm fm).program
  let fm' := (e.subst p vm fm).funMap
  let hsize := (e.subst p vm fm).props.pre.size_le
  have hvalid' : p'.ValidSubst vm.extend fm' :=
    Program.validSubst_subst hvm hfm hp hvalid ho
  obtain ⟨k, hk, hf, ⟨hkk', hf'⟩ | ⟨hfmk, hne⟩⟩ :=
    Expr.free_of_free_in_subst hvm hfm hp hvalid hwf Program.wfSubst_mk ho hwfs hf
  · by_cases n = k
    · subst k
      simp only [VarMap.mk, Vector.getElem_setIfInBounds_self, vm] at hf'
      exact Or.inr hf'
    · simp [VarMap.mk, vm, *] at hf'
      have .var := hf'
      exact Or.inl ⟨hf, ‹n ≠ m›.symm⟩
  · have hkk' : fm'[k] = k := by
      apply hvalid'.eq_of_not_nests
      intro l hl hvml hnests
      obtain rfl : n = l := by grind
      replace hnests : n ≻[p] k := by grind
      exact hnnests _ hf hnests
    rw [hfmk] at hkk'
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
