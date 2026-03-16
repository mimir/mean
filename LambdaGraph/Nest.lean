import LambdaGraph.Basic

/--
The free-variable relation.

A variable occurs free in an expression if the expression itself contains the
variable, or if it contains a reference to a function in which the variable
occurs free.

By using an inductive proposition, we guarantee that free variable derivations
must be finite, so that a derivation always points in finitely many steps to an
actual occurrence of the variable. This means this definition matches the
paper's definition of free variable sets as a least fixed point.
-/
inductive Expr.Free (p : Program) (n : Nat) : Expr → Prop where
  | var : Free p n (.var n)
  | fn (m : Nat) (_ : m < p.size) : n ≠ m → Free p n p.fn[m] → Free p n (.fn m)
  | binL (k : BinKind) (e₁ e₂ : Expr) : Free p n e₁ → Free p n (e₁.bin k e₂)
  | binR (k : BinKind) (e₁ e₂ : Expr) : Free p n e₂ → Free p n (e₁.bin k e₂)
  | condC (c et ef : Expr) : Free p n c → Free p n (c.cond et ef)
  | condT (c et ef : Expr) : Free p n et → Free p n (c.cond et ef)
  | condF (c et ef : Expr) : Free p n ef → Free p n (c.cond et ef)
  | proj (e : Expr) (i : Fin 2) : Free p n e → Free p n (e.proj i)

/--
The nesting relation between functions in a program.

During substitution, functions nested in the function corresponding to the
substitution variable need to be rewritten if they are reachable.

This corresponds to the strict nesting relation ≻ in the paper.
-/
inductive Program.Nests (p : Program) : Nat → Nat → Prop where
  | free (n m : Nat) (_ : n < p.size) (_ : m < p.size) :
    n ≠ m → p.fn[m].Free p n → Nests p n m
  | trans (n m k : Nat) : Nests p n m → Nests p m k → Nests p n k

attribute [grind →] Program.Nests.trans

notation:40 n:41 " ≻[" p:min "] " m:41 => Program.Nests p n m
notation:40 n:41 " ⊁[" p:min "] " m:41 => ¬n ≻[p] m

/--
The reflexive closure of the nesting relation.

This corresponds to the non-strict nesting relation ≽ in the paper.
-/
inductive Program.NestsEq (p : Program) (n : Nat) : Nat → Prop where
  | refl (_ : n < p.size) : NestsEq p n n
  | nests (m : Nat) : Nests p n m → NestsEq p n m

notation:40 n:41 " ≽[" p:min "] " m:41 => Program.NestsEq p n m
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
def Expr.Closed (p : Program) (e : Expr) : Prop := ∀ ⦃n⦄, ¬e.Free p n

/--
A program is well-formed if no function nests itself.

This corresponds to Property 2 from the paper, but is formulated in terms of the
strict nesting relation instead. The theorem `Program.wf_iff` shows that the two
definitions are equivalent.
-/
def Program.WF (p : Program) : Prop := ∀ ⦃n⦄, n ⊁[p] n

/--
Free variables of a computation.

A variable occurs free in a computation if it occurs free in the computation's
expression.
-/
def Computation.Free (c : Computation) (n : Nat) := c.expr.Free c.toProgram n

/-- A computation is closed if its expression is closed in its program. -/
def Computation.Closed (c : Computation) : Prop := c.expr.Closed c.toProgram

@[simp, grind .]
theorem Expr.not_free_in_const {p : Program} {c : Const} {n : Nat} :
    ¬(const c).Free p n := nofun

@[simp, grind =]
theorem Expr.free_in_bin_iff {p : Program} {k : BinKind} {e₁ e₂ : Expr}
    {n : Nat} : (e₁.bin k e₂).Free p n ↔ e₁.Free p n ∨ e₂.Free p n := by
  constructor
  · intro h
    cases h <;> solve_by_elim [Or.inl, Or.inr]
  · rintro (hf | he) <;> solve_by_elim [Free.binL, Free.binR]

@[simp, grind =]
theorem Expr.free_in_cond_iff {p : Program} {c et ef : Expr} {n : Nat} :
    (c.cond et ef).Free p n ↔ c.Free p n ∨ et.Free p n ∨ ef.Free p n := by
  constructor
  · intro h
    cases h <;> solve_by_elim [Or.inl, Or.inr]
  · rintro (hc | het | hef) <;> solve_by_elim [Free.condC, Free.condT, Free.condF]

@[simp, grind =]
theorem Expr.free_in_proj_iff {p : Program} {e : Expr} {i : Fin 2} {n : Nat} :
    (e.proj i).Free p n ↔ e.Free p n := by
  constructor
  · intro h
    have .proj _ _ h := h
    exact h
  · intro h
    exact .proj _ _ h

@[simp]
theorem Expr.not_closed_var {p : Program} {n : Nat} : ¬(Expr.var n).Closed p :=
  fun h => h .var

@[simp]
theorem Expr.bin_closed_iff {p : Program} {k : BinKind} {e₁ e₂ : Expr} :
    (e₁.bin k e₂).Closed p ↔ e₁.Closed p ∧ e₂.Closed p := by
  constructor
  · intro h
    constructor <;> solve_by_elim [Free.binL, Free.binR]
  · rintro ⟨h₁, h₂⟩ n (- | -) <;> solve_by_elim

@[simp]
theorem Expr.cond_closed_iff {p : Program} {c et ef : Expr} :
    (c.cond et ef).Closed p ↔ c.Closed p ∧ et.Closed p ∧ ef.Closed p := by
  constructor
  · intro h
    open Expr.Free in
    and_intros <;> solve_by_elim [condC, condT, condF]
  · rintro ⟨hc, het, hef⟩ n (- | - | -) <;> solve_by_elim

@[simp]
theorem Expr.proj_closed_iff {p : Program} {e : Expr} {i : Fin 2} :
    (e.proj i).Closed p ↔ e.Closed p := by
  constructor
  · intro h n hf
    exact h (.proj _ _ hf)
  · intro h n hf
    have .proj _ _ hf := hf
    exact h hf

@[grind →]
theorem Expr.lt_size_of_free {p : Program} {e : Expr} {n : Nat}
    (hp : p.ValidRefs) (he : e.ValidRefs p) (hf : e.Free p n) : n < p.size := by
  induction hf with simp_all <;> solve_by_elim

@[grind →]
theorem Program.lt_size_left_of_nests {p : Program} {m n : Nat} :
    m ≻[p] n → m < p.size
  | .free _ _ hn _ _ _ => hn
  | .trans _ _ _ h _ => lt_size_left_of_nests h

@[grind →]
theorem Program.lt_size_right_of_nests {p : Program} {m n : Nat} :
    n ≻[p] m → m < p.size
  | .free _ _ _ hm _ _ => hm
  | .trans _ _ _ _ h => lt_size_right_of_nests h

@[grind →]
theorem Program.lt_size_left_of_nestsEq {p : Program} {m n : Nat} :
    m ≽[p] n → m < p.size
  | .refl h => h
  | .nests _ h => lt_size_left_of_nests h

theorem Program.nests_iff {p : Program} {m n : Nat} : m ≻[p] n ↔
    ∃ (_ : n < p.size) (k : Nat), k < p.size ∧ k ≠ n ∧ p.fn[n].Free p k ∧ m ≽[p] k := by
  constructor
  · intro h
    induction h with
    | free k n hk hn hne hf => exact ⟨hn, k, hk, hne, hf, .refl hk⟩
    | trans n m k h₁ h₂ ih₁ ih₂ =>
      obtain ⟨hk, l, hl, hne, hf, h⟩ := ih₂
      cases h with
      | refl => exact ⟨hk, m, hl, hne, hf, .nests _ h₁⟩
      | nests _ h => exact ⟨hk, l, hl, hne, hf, .nests _ (.trans _ _ _ h₁ h)⟩
  · rintro ⟨hn, k, hk, hne, hf, h⟩
    cases h with
    | refl => exact .free _ _ hk hn hne hf
    | nests _ h => exact .trans _ _ _ h (.free _ _ hk hn hne hf)

/--
Proves that our definition of well-formedness in terms of the strict nesting
relation is equivalent to the paper's definition, which uses the non-strict
nesting relation.
-/
theorem Program.wf_iff {p : Program} :
    p.WF ↔ ∀ {m n}, m ≽[p] n → n ≽[p] m → m = n := by
  constructor
  · intro h m n hnests₁ hnests₂
    match hnests₁, hnests₂ with
    | .refl _, _ | _, .refl _ => rfl
    | .nests _ hnests₁, .nests _ hnests₂ =>
      exfalso
      exact h (.trans _ _ _ hnests₁ hnests₂)
  · intro h n hnests
    replace ⟨hn, k, hk, hne, hf, hnests⟩ := nests_iff.mp hnests
    exact hne (h (.nests _ (.free _ _ hk hn hne hf)) hnests)

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
          | solve_by_elim [var, binL, binR, condC, condT, condF, proj]

theorem Expr.free_of_localFn_of_free {p : Program} {e : Expr} {m n : Nat}
    (hm : m < p.size) (hne : n ≠ m) (hlf : e.LocalFn m)
    (hf : p.fn[m].Free p n) : e.Free p n := by
  unfold LocalFn at hlf
  generalize hr : RefKind.fn = r at hlf
  open Free in
  induction hlf with
    first | contradiction
          | solve_by_elim [var, binL, binR, condC, condT, condF, proj]

theorem Expr.free_iff {p : Program} {e : Expr} {n : Nat} :
    e.Free p n ↔
      e.LocalVar n ∨ ∃ (m k : Nat) (_ : k < p.size),
        e.LocalFn m ∧ m ⟶[p, n]* k ∧ p.fn[k].LocalVar n := by
  constructor
  · intro h
    induction h with try grind
    | fn m hm hne hf ih =>
      refine Or.inr ⟨m, ?_⟩
      obtain hlv | ⟨k, l, hl, hlf, hp, hlv⟩ := ih
      · exact ⟨m, hm, .fn, .refl _ hne, hlv⟩
      · exact ⟨l, hl, .fn, .step _ _ _ hne ⟨hm, hlf⟩ hp, hlv⟩
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

theorem Program.free_eq_of_local_eq {p : Program} {i : Nat} (hi : i < p.size)
    (h : ∀ k r, p.fn[i].Local k r → k = i) {n : Nat} (hf : p.fn[i].Free p n) :
    n = i := by
  false_or_by_contra
  rename_i hne
  obtain ⟨k, hk, hlv, hpath⟩ := (free_in_fn_iff hi hne).mp hf
  induction hpath with
  | refl i => solve_by_elim
  | step i l k hne hs hpath ih =>
    obtain ⟨_, hlf⟩ := hs
    have := h _ _ hlf
    subst l
    apply ih hi h hf hne hk hlv

theorem Expr.free_in_setBody {p : Program} {i : Nat} {b e : Expr}
    (hi : i < p.size) (h : ∀ k r, p.fn[i].Local k r → k = i) {n : Nat}
    (hf : e.Free p n) : e.Free (p.setBody i b) n := by
  induction hf with
    try solve_by_elim [Free.binL, Free.binR, Free.condC, Free.condT, Free.condF]
  | fn m hm hne hf ih =>
    refine .fn _ hm hne ?_
    by_cases i = m
    · subst m
      have := Program.free_eq_of_local_eq hi h hf
      contradiction
    · simp [*]

theorem Program.nests_in_setBody {p : Program} {i : Nat} {b : Expr}
    (hi : i < p.size) (h : ∀ k r, p.fn[i].Local k r → k = i) {n m : Nat}
    (hnests : n ≻[p] m) : n ≻[p.setBody i b] m := by
  induction hnests with
  | free n m hn hm hne hf =>
    have : i ≠ m := by
      intro rfl
      have := free_eq_of_local_eq _ h hf
      contradiction
    rw [show p.fn[m] = (p.setBody i b).fn[m] by simp [*]] at hf
    exact .free _ _ hn hm hne (Expr.free_in_setBody hi h hf)
  | trans => grind

theorem Expr.free_in_prefix_iff {p p' : Program} {e : Expr} {n : Nat}
    (hp : p.ValidRefs) (he : e.ValidRefs p) (h : p.Prefix p') :
    e.Free p' n ↔ e.Free p n := by
  have hle := h.size_le
  constructor
  · intro hf
    induction hf with grind [intro Free]
  · intro hf
    induction hf with grind [intro Free]

grind_pattern Expr.free_in_prefix_iff => p.Prefix p', e.ValidRefs p, e.Free p n
grind_pattern Expr.free_in_prefix_iff => p.Prefix p', e.ValidRefs p, e.Free p' n

theorem Program.pathWithout_in_prefix_iff {p p'} {n m k : Nat}
    (hn : n < p.size) (hp : p.ValidRefs) (h : p.Prefix p') :
    n ⟶[p', m]* k ↔ n ⟶[p, m]* k := by
  constructor
  · intro hpath
    induction hpath with
    | refl n hne => exact .refl _ hne
    | step n l k hne hs hpath ih =>
      obtain ⟨_, hlf⟩ := hs
      rw [h.fn_eq hn] at hlf
      exact .step _ _ _ hne ⟨hn, hlf⟩ (ih (hp hn hlf))
  · intro hpath
    induction hpath with
    | refl n hne => exact .refl _ hne
    | step n l k hne hs hpath ih =>
      obtain ⟨_, hlf⟩ := hs
      exact .step _ _ _ hne ⟨by grind, h.fn_eq hn ▸ hlf⟩ (ih (hp hn hlf))

grind_pattern Program.pathWithout_in_prefix_iff => p.Prefix p', n ⟶[p, m]* k
grind_pattern Program.pathWithout_in_prefix_iff => p.Prefix p', n ⟶[p', m]* k

theorem Program.nests_in_prefix_iff {p p' : Program} {n m : Nat}
    (hm : m < p.size) (hp : p.ValidRefs) (h : p.Prefix p') :
    n ≻[p'] m ↔ n ≻[p] m := by
  constructor
  · intro hnests
    induction hnests with
    | free n m hn hm hne hf =>
      rw [h.fn_eq hm] at *
      exact .free _ _ (by grind) hm hne ((Expr.free_in_prefix_iff hp (hp hm) h).mp hf)
    | trans => grind
  · intro hnests
    induction hnests with
    | free n m hn hm hne hf =>
      exact .free _ _ (by grind) (by grind) hne <|
        (Expr.free_in_prefix_iff hp (h.fn_eq hm ▸ hp hm) h).mpr (h.fn_eq hm ▸ hf)
    | trans => grind

grind_pattern Program.nests_in_prefix_iff => p.Prefix p', n ≻[p] m
grind_pattern Program.nests_in_prefix_iff => p.Prefix p', n ≻[p'] m

theorem Program.nestsEq_in_prefix_iff {p p' : Program} {n m : Nat}
    (hm : m < p.size) (hp : p.ValidRefs) (h : p.Prefix p') :
    n ≽[p'] m ↔ n ≽[p] m := by
  constructor <;> rintro (hnests | hnests) <;> grind [intro NestsEq]

grind_pattern Program.nestsEq_in_prefix_iff => p.Prefix p', n ≽[p] m
grind_pattern Program.nestsEq_in_prefix_iff => p.Prefix p', n ≽[p'] m

theorem Program.free_in_fn_of_succ {p : Program} {m n k : Nat} (hn : n < p.size)
    (hne : k ≠ n) (hs : m ⟶[p] n) (hf : p.fn[n].Free p k) :
    (p.fn[m]'hs.1).Free p k :=
  have ⟨_, hlf⟩ := hs
  Expr.free_of_localFn_of_free hn hne hlf hf

theorem Program.free_in_fn_of_pathWithout {p : Program} {m n k : Nat}
    (hm : m < p.size) (hk : k < p.size) (hp : m ⟶[p, n]* k)
    (hf : p.fn[k].Free p n) : p.fn[m].Free p n := by
  obtain ⟨l, hl, hlv, hp'⟩ := (free_in_fn_iff hk hp.ne_end).mp hf
  apply (free_in_fn_iff hm hp.ne_start).mpr
  exact ⟨l, hl, hlv, pathWithout_trans hp hp'⟩

/--
Free variables can be pulled back along CFG edges.

Corresponds to Lemma 1 in the paper.
-/
theorem Expr.free_in_fn_of_succ {p : Program} {m n k : Nat}
    (hne : k ≠ m) (hs : m ⟶[p] n) : (fn n).Free p k → (fn m).Free p k
  | .fn _ hn hne' hf =>
    .fn _ hs.1 hne (Program.free_in_fn_of_succ hn hne' hs hf)

/--
Free variables can be pulled back along paths through the CFG.

Corresponds to Lemma 2 in the paper.
-/
theorem Expr.free_in_fn_of_pathWithout {p : Program} {m n k : Nat}
    (hp : m ⟶[p, n]* k) : (fn k).Free p n → (fn m).Free p n
  | .fn _ hk _ hf =>
    have hm : m < p.size :=
      match hp with
      | .refl _ _ => hk
      | .step _ _ _ _ hs _ => hs.1
    .fn _ hm hp.ne_start (Program.free_in_fn_of_pathWithout hm hk hp hf)

theorem Program.dominates_of_nests {p : Program} {m n k : Nat}
    (hwf : p.WF) (hmn : m ≻[p] n) (hnk : n ≻[p] k) : p.Dominates m n k := by
  induction hnk with
  | free n k hn hk hne hfk =>
    intro hp
    have hm := lt_size_left_of_nests hmn
    have hfm := free_in_fn_of_pathWithout hm hk hp hfk
    have hnm : n ≻[p] m := .free _ _ hn _ hp.ne_start hfm
    exact hwf (.trans _ _ _ hmn hnm)
  | trans n l k hnl hlk ih₁ ih₂ =>
    apply_rules [dominates_trans, Nests.trans]

/-- Nesting implies dominance. Corresponds to Theorem 1 in the paper. -/
theorem Program.dominates_of_nestsEq {p : Program} {m n k : Nat}
    (hwf : p.WF) (hmn : m ≽[p] n) (hnk : n ≽[p] k) : p.Dominates m n k :=
  match hmn, hnk with
  | .refl _, _ => fun h => nomatch h.ne_start
  | _, .refl _ => fun h => nomatch h.ne_end
  | .nests _ h₁, .nests _ h₂ => dominates_of_nests hwf h₁ h₂
