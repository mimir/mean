import LambdaGraph.Basic

/--
The free-variable relation.

A variable occurs free in an expression if the expression itself contains the
variable, or if it contains a reference to a function in which the variable
occurs free.
-/
inductive Expr.Free (p : Program) (n : Nat) : Expr → Prop where
  | var : Free p n (.var n)
  | fn (m : Nat) (_ : m < p.size) : n ≠ m → Free p n p.fn[m] → Free p n (.fn m)
  | appL (f e : Expr) : Free p n f → Free p n (.app f e)
  | appR (f e : Expr) : Free p n e → Free p n (.app f e)
  | condC (c et ef : Expr) : Free p n c → Free p n (.cond c et ef)
  | condT (c et ef : Expr) : Free p n et → Free p n (.cond c et ef)
  | condF (c et ef : Expr) : Free p n ef → Free p n (.cond c et ef)

/--
The nesting relation between functions in a program.

During substitution, all functions nested in the function corresponding to the
substitution variable must be rewritten.
-/
inductive Nests (p : Program) (n : Nat) : Nat → Prop where
  | free (m : Nat) (_ : m < p.size) : n ≠ m → p.fn[m].Free p n → Nests p n m
  | step (m k : Nat) (_ : k < p.size) :
    m ≠ k → p.fn[k].Free p m → Nests p n m → Nests p n k

notation:40 n:41 " ≻[" p:min "] " m:41 => Nests p n m
notation:40 n:41 " ⊁[" p:min "] " m:41 => ¬n ≻[p] m

/-- The reflexive closure of the nesting relation. -/
inductive NestsEq (p : Program) (n : Nat) : Nat → Prop where
  | refl (_ : n < p.size) : NestsEq p n n
  | nests (m : Nat) : Nests p n m → NestsEq p n m

notation:40 n:41 " ≽[" p:min "] " m:41 => NestsEq p n m
notation:40 n:41 " ⋡[" p:min "] " m:41 => ¬n ≽[p] m

/--
The successor relation between functions.

A function is a successor (in the CFG) of another function if it occurs in that
function's body (loops are permitted).
-/
def Program.Succ (p : Program) (m n : Nat) :=
  ∃ (_ : m < p.size), p.fn[m].LocalFn n

notation:40 m:41 " ⟶[" p:min "] " n:41 => Program.Succ p m n

/--
A path from one function to another, in which the function `l` does not occur.

Longer paths are constructed by prepending edges to the beginning, matching how
the free variable relation can add extra function references on the “outside” of
an expression.
-/
inductive Program.PathWithout (p : Program) (l : Nat) : Nat → Nat → Prop where
  | refl n : l ≠ n → p.PathWithout l n n
  | step m n k : l ≠ m → m ⟶[p] n → p.PathWithout l n k → p.PathWithout l m k

notation:40 m:41 " ⟶[" p:min ", " l:min "]* " n:41 => Program.PathWithout p l m n

/--
A function `n` dominates `k` if no path from the start `m` to `k` can avoid `n`.

This relation can also be read as post-dominance with end `k`.
-/
def Program.Dominates (p : Program) (m n k : Nat) : Prop := ¬m ⟶[p, n]* k

/-- An expression is closed if it has no free variables. -/
def Expr.Closed (p : Program) (e : Expr) : Prop := ∀ n, ¬e.Free p n

/-- A program is well-formed if no function nests itself. -/
def Program.WF (p : Program) : Prop := ∀ n, n ⊁[p] n

/--
Free variables of a computation.

A variable occurs free in a computation if it occurs free in the computation's
expression.
-/
def Computation.Free (p : Computation) (n : Nat) := p.expr.Free p.toProgram n

/-- A computation is closed if its expression is closed in its program. -/
def Computation.Closed (p : Computation) : Prop := ∀ n, ¬p.Free n

@[simp]
theorem not_closed_var {p : Program} {n : Nat} : ¬(Expr.var n).Closed p :=
  fun h => h n .var

theorem fn_closed_iff {p : Program} {m : Nat} :
    (Expr.fn m).Closed p ↔ ∀ n ≠ m, (_ : m < p.size) → ¬p.fn[m].Free p n := by
  constructor
  · intro hc n hn _
    intro hne
    solve_by_elim
  · intro hf n hn
    cases hn with
    | fn _ _ hne hn =>
      solve_by_elim

@[simp]
theorem app_closed_iff {p : Program} {f e : Expr} :
    (f.app e).Closed p ↔ f.Closed p ∧ e.Closed p := by
  constructor
  · intro h
    constructor <;> solve_by_elim [Expr.Free.appL, Expr.Free.appR]
  · rintro ⟨hf, he⟩ n (- | -) <;> solve_by_elim

@[simp]
theorem bool_closed (p : Program) (b : Bool) : (Expr.bool b).Closed p := nofun

@[simp]
theorem cond_closed_iff {p : Program} {c et ef : Expr} :
    (c.cond et ef).Closed p ↔ c.Closed p ∧ et.Closed p ∧ ef.Closed p := by
  constructor
  · intro h
    open Expr.Free in
    and_intros <;> solve_by_elim [condC, condT, condF]
  · rintro ⟨hc, het, hef⟩ n (- | - | -) <;> solve_by_elim

theorem lt_size_of_free {p : Program} {e : Expr} {n : Nat} (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hf : e.Free p n) : n < p.size := by
  induction hf with simp_all <;> solve_by_elim

theorem lt_size_left_of_nests {p : Program} {m n : Nat} (hp : p.ValidRefs)
    (h : m ≻[p] n) : m < p.size := by
  induction h with solve_by_elim [lt_size_of_free]

theorem lt_size_right_of_nests {p : Program} {m n : Nat} : n ≻[p] m → m < p.size
  | .free _ hm _ _ => hm
  | .step _ _ hm _ _ _ => hm

theorem lt_size_left_of_nestsEq {p : Program} {m n : Nat} (hp : p.ValidRefs) :
    m ≽[p] n → m < p.size
  | .refl h => h
  | .nests _ h => lt_size_left_of_nests hp h

theorem nests_self {p : Program} {n : Nat} :
    (h : n ≻[p] n) → ∃ m ≠ n, (p.fn[n]'(lt_size_right_of_nests h)).Free p m
  | .free _ _ hne _ => nomatch hne
  | .step k _ _ hne hf _ => ⟨k, hne, hf⟩

theorem nests_trans {p : Program} {m n k : Nat} (h : m ≻[p] n) (h' : n ≻[p] k) :
    m ≻[p] k := by
  induction h' with apply Nests.step <;> assumption

theorem Program.pathWithout_trans {p : Program} {m n k l : Nat}
    (h : m ⟶[p, l]* n) (h' : n ⟶[p, l]* k) : m ⟶[p, l]* k := by
  induction h with
  | refl => assumption
  | step m n o hne hs hp ih => constructor <;> apply_rules

theorem Program.PathWithout.ne_start {p : Program} {m n k : Nat}
    (h : p.PathWithout k m n) : k ≠ m := by
  intro rfl
  cases h <;> contradiction

theorem Program.PathWithout.ne_end {p : Program} {m n k : Nat}
    (h : p.PathWithout k m n) : k ≠ n := by
  induction h <;> trivial

theorem Program.eq_of_dominates_start {p : Program} {m n : Nat}
    (h : p.Dominates m n m) : n = m := by
  apply Decidable.byContradiction
  intro hne
  exact h (.refl _ hne)

theorem Program.dominates_trans {p : Program} {m n k l : Nat}
    (h : p.Dominates m n k) (h' : p.Dominates m k l) : p.Dominates m n l := by
  intro hpml
  induction hpml with
  | refl m =>
    obtain rfl := eq_of_dominates_start h'
    obtain rfl := eq_of_dominates_start h
    contradiction
  | step m o l hnm hs hpol ih =>
    by_cases hkm : k = m
    · subst k
      exact h (.refl _ hnm)
    · apply ih
      · intro hpok
        exact h (.step _ _ _ hnm hs hpok)
      · intro hpol
        exact h' (.step _ _ _ hkm hs hpol)

theorem Expr.free_of_localVar {p : Program} {e : Expr} {n : Nat}
    (h : e.LocalVar n) : e.Free p n := by
  unfold LocalVar at h
  generalize hr : RefKind.var = r at h
  open Free in
  induction h with
    first | contradiction
          | solve_by_elim [var, appL, appR, condC, condT, condF]

theorem Expr.free_of_localFn_of_free {p : Program} {e : Expr} {m n : Nat}
    (hm : m < p.size) (hne : n ≠ m) (hlf : e.LocalFn m)
    (hf : p.fn[m].Free p n) : e.Free p n := by
  unfold LocalFn at hlf
  generalize hr : RefKind.fn = r at hlf
  open Free in
  induction hlf with
    first | contradiction
          | solve_by_elim [var, appL, appR, condC, condT, condF]

theorem Program.free_in_fn_of_succ {p : Program} {m n k : Nat} (hm : m < p.size)
    (hn : n < p.size) (hne : k ≠ n) (hs : m ⟶[p] n) (hf : p.fn[n].Free p k) :
    p.fn[m].Free p k :=
  have ⟨_, hlf⟩ := hs
  Expr.free_of_localFn_of_free hn hne hlf hf

theorem Expr.free_iff {p : Program} {e : Expr} {n : Nat} :
    e.Free p n ↔
      e.LocalVar n ∨ ∃ (m k : Nat) (_ : k < p.size),
        e.LocalFn m ∧ m ⟶[p, n]* k ∧ p.fn[k].LocalVar n := by
  constructor
  · intro h
    induction h with
    | var => left; constructor
    | fn m hm hne hf ih =>
      refine Or.inr ⟨m, ?_⟩
      obtain hlv | ⟨k, l, hl, hlf, hp, hlv⟩ := ih
      · exact ⟨m, hm, .fn, .refl _ hne, hlv⟩
      · exact ⟨l, hl, .fn, .step _ _ _ hne ⟨hm, hlf⟩ hp, hlv⟩
    | appL => grind [Local.appL]
    | appR => grind [Local.appR]
    | condC => grind [Local.condC]
    | condT => grind [Local.condT]
    | condF => grind [Local.condF]
  · rintro (hlv | ⟨m, k, hk, hlf, hp, hlv⟩)
    · exact free_of_localVar hlv
    · have hf : p.fn[k].Free p n := free_of_localVar hlv
      induction hp generalizing e with
      | refl m hne => exact free_of_localFn_of_free hk hne hlf hf
      | step m l k hne hs hp ih =>
        obtain ⟨hm, hlf'⟩ := hs
        apply free_of_localFn_of_free hm hne hlf (ih hk hlf' hlv hf)

theorem Program.free_in_fn_iff {p : Program} {m n : Nat} (hm : m < p.size)
    (hne : n ≠ m) : p.fn[m].Free p n ↔
      ∃ (k : Nat) (_ : k < p.size),
        p.fn[k].LocalVar n ∧ m ⟶[p, n]* k := by
  constructor
  · intro hf
    obtain hlv | ⟨k, l, hl, hlf, hp, hlv⟩ := Expr.free_iff.mp hf
    · exact ⟨m, hm, hlv, .refl _ hne⟩
    · exact ⟨l, hl, hlv, .step _ _ _ hne ⟨hm, hlf⟩ hp⟩
  · intro ⟨k, hk, hlv, hp⟩
    cases hp with
    | refl m => exact Expr.free_of_localVar hlv
    | step m l k hne hs hp =>
      obtain ⟨_, hlf⟩ := hs
      exact Expr.free_iff.mpr <| Or.inr ⟨l, k, hk, hlf, hp, hlv⟩

theorem Program.free_of_pathWithout_of_free {p : Program} {m n k : Nat}
    (hm : m < p.size) (hk : k < p.size) (hp : m ⟶[p, n]* k)
    (hf : p.fn[k].Free p n) : p.fn[m].Free p n := by
  obtain ⟨l, hl, hlv, hp'⟩ := (free_in_fn_iff hk hp.ne_end).mp hf
  apply (free_in_fn_iff hm hp.ne_start).mpr
  exact ⟨l, hl, hlv, pathWithout_trans hp hp'⟩

theorem Program.dominates_of_nests {p : Program} {m n k : Nat}
    (hv : p.ValidRefs) (hwf : p.WF) (hmn : m ≻[p] n) (hnk : n ≻[p] k) :
    p.Dominates m n k := by
  induction hnk with
  | free k hk hne hfk =>
    intro hp
    have hm := lt_size_left_of_nests hv hmn
    have hfm := free_of_pathWithout_of_free hm hk hp hfk
    have hnm : n ≻[p] m := by
      constructor
      · intro rfl
        exact hwf _ hmn
      · exact hfm
    exact hwf _ (nests_trans hmn hnm)
  | step l k hk hne hfk hnl ih =>
    apply dominates_trans ih
    intro hp
    have hm := lt_size_left_of_nests hv hmn
    have hfm := free_of_pathWithout_of_free hm hk hp hfk
    have hlm : l ≻[p] m := by
      constructor
      · intro rfl
        exact hwf _ (nests_trans hnl hmn)
      · exact hfm
    exact hwf _ (nests_trans hmn (nests_trans hnl hlm))

theorem Program.dominates_of_nestsEq {p : Program} {m n k : Nat}
    (hv : p.ValidRefs) (hwf : p.WF) (hmn : m ≽[p] n) (hnk : n ≽[p] k) :
    p.Dominates m n k :=
  match hmn, hnk with
  | .refl _, _ => fun h => nomatch h.ne_start
  | .nests _ _, .refl _ => fun h => nomatch h.ne_end
  | .nests _ h₁, .nests _ h₂ => dominates_of_nests hv hwf h₁ h₂
