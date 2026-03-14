import LambdaGraph.Subst

/-- The small-step reduction relation. -/
inductive Computation.Step : Computation → Computation → Prop where
  | appFn (p : Program) (n : Nat) (e : Expr) (_ : n < p.size) :
    e.Value → Step ⟨p, .app (.fn n) e⟩ (.subst ⟨p, p.fn[n]⟩ n e)
  | appOp (p : Program) (f : Op) (x y : Int) :
    Step ⟨p, .app f (.pair x y)⟩ ⟨p, ⟦f⟧ x y⟩
  | appCmp (p : Program) (f : Cmp) (x y : Int) :
    Step ⟨p, .app f (.pair x y)⟩ ⟨p, ⟦f⟧ x y⟩
  | appLogic (p : Program) (f : Logic) (b₁ b₂ : Bool) :
    Step ⟨p, .app f (.pair b₁ b₂)⟩ ⟨p, ⟦f⟧ b₁ b₂⟩
  | binL (p p' : Program) (k : BinKind) (e₁ e₁' e₂ : Expr) :
    Step ⟨p, e₁⟩ ⟨p', e₁'⟩ → Step ⟨p, e₁.bin k e₂⟩ ⟨p', e₁'.bin k e₂⟩
  | binR (p p' : Program) (k : BinKind) (e₁ e₂ e₂' : Expr) :
    e₁.Value → Step ⟨p, e₂⟩ ⟨p', e₂'⟩ → Step ⟨p, e₁.bin k e₂⟩ ⟨p', e₁.bin k e₂'⟩
  | condT (p : Program) (et ef : Expr) :
    Step ⟨p, (.cond true et ef)⟩ ⟨p, et⟩
  | condF (p : Program) (et ef : Expr) :
    Step ⟨p, (.cond false et ef)⟩ ⟨p, ef⟩
  | condC (p p' : Program) (c c' et ef : Expr) :
    Step ⟨p, c⟩ ⟨p', c'⟩ → Step ⟨p, c.cond et ef⟩ ⟨p', c'.cond et ef⟩
  | proj0 (p : Program) (e₁ e₂ : Expr) :
    e₁.Value → e₂.Value → Step ⟨p, .proj (.pair e₁ e₂) 0⟩ ⟨p, e₁⟩
  | proj1 (p : Program) (e₁ e₂ : Expr) :
    e₁.Value → e₂.Value → Step ⟨p, .proj (.pair e₁ e₂) 1⟩ ⟨p, e₂⟩
  | proj (p p' : Program) (e e' : Expr) (i : Fin 2) :
    Step ⟨p, e⟩ ⟨p', e'⟩ → Step ⟨p, e.proj i⟩ ⟨p', e'.proj i⟩

notation:40 c:41 " ⇒ " c':41 => Computation.Step c c'

/-- The reflexive-transitive closure of the reduction relation. -/
inductive Computation.Steps : Computation → Computation → Prop where
  | refl (c : Computation) : Steps c c
  | step (c c' c'' : Computation) : Step c c' → Steps c' c'' → Steps c c''

notation:40 c:41 " ⇒* " c':41 => Computation.Steps c c'

namespace Computation

theorem size_le_of_step {c c' : Computation} (h : c ⇒ c') :
    c.size ≤ c'.size := by
  induction h with simp [subst, SubstResult.size_ge, *]

theorem lt_size_of_step {c c' : Computation} {n : Nat} (hn : n < c.size)
    (h : c ⇒ c') : n < c'.size := Nat.lt_of_lt_of_le hn (size_le_of_step h)

theorem fn_eq_of_step {c c' : Computation} {n : Nat} (hn : n < c.size)
    (h : c ⇒ c') : c.fn[n] = c'.fn[n]'(lt_size_of_step hn h) := by
  induction h with simp [subst, Program.subst_fn_eq_of_lt hn, *]

theorem ty_eq_of_step {c c' : Computation} {n : Nat} (hn : n < c.size)
    (h : c ⇒ c') : c.ty[n] = c'.ty[n]'(lt_size_of_step hn h) := by
  induction h with simp [subst, Program.subst_ty_eq_of_lt hn, *]

theorem ret_eq_of_step {c c' : Computation} {n : Nat} (hn : n < c.size)
    (h : c ⇒ c') : c.ret[n] = c'.ret[n]'(lt_size_of_step hn h) := by
  induction h with simp [subst, Program.subst_ret_eq_of_lt hn, *]

theorem types_of_step {c c' : Computation} {e : Expr} {t : Ty}
    (ht : c.toProgram ⊢ e : t) (hs : c ⇒ c') : c'.toProgram ⊢ e : t := by
  induction ht with try constructor <;> assumption
  | var n hn => rw [ty_eq_of_step hn hs]; constructor
  | fn n hn => rw [ty_eq_of_step hn hs, ret_eq_of_step hn hs]; constructor

end Computation

/-- The progress theorem. Corresponds to Theorem 2 in the paper. -/
theorem Computation.progress {c : Computation} {t : Ty}
    (hte : c.toProgram ⊢ c.expr : t) (hc : c.Closed) :
    c.expr.Value ∨ ∃ c', c ⇒ c' := by
  obtain ⟨p, e⟩ := c
  simp only at *
  induction hte with
  | var n hn => simp [Closed] at hc
  | fn n hn => left; constructor
  | const c => left; constructor
  | app f e t₁ t₂ htf hte ihf ihe =>
    right
    obtain ⟨hcf, hce⟩ := Expr.bin_closed_iff.mp hc
    obtain hvf | ⟨c', hs⟩ := ihf hcf
    · obtain hve | ⟨c', hs⟩ := ihe hce
      · obtain ⟨n, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩ :=
          Expr.value_types_fn htf hvf
        · have .fn _ hn := htf
          exact ⟨_, Step.appFn _ _ _ hn hve⟩
        · have .const _ := htf
          obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := Expr.value_types_prod hte hve
          have .pair _ _ _ _ ht₁ ht₂ := hte
          obtain ⟨x, rfl⟩ := Expr.value_types_int ht₁ hv₁
          obtain ⟨y, rfl⟩ := Expr.value_types_int ht₂ hv₂
          exact ⟨_, Step.appOp _ _ _ _⟩
        · have .const _ := htf
          obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := Expr.value_types_prod hte hve
          have .pair _ _ _ _ ht₁ ht₂ := hte
          obtain ⟨x, rfl⟩ := Expr.value_types_int ht₁ hv₁
          obtain ⟨y, rfl⟩ := Expr.value_types_int ht₂ hv₂
          exact ⟨_, Step.appCmp _ _ _ _⟩
        · have .const _ := htf
          obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := Expr.value_types_prod hte hve
          have .pair _ _ _ _ ht₁ ht₂ := hte
          obtain ⟨b₁, rfl⟩ := Expr.value_types_bool ht₁ hv₁
          obtain ⟨b₂, rfl⟩ := Expr.value_types_bool ht₂ hv₂
          exact ⟨_, Step.appLogic _ _ _ _⟩
      · exact ⟨_, Step.binR _ _ _ _ _ _ hvf hs⟩
    · exact ⟨_, Step.binL _ _ _ _ _ _ hs⟩
  | pair e₁ e₂ t₁ t₂ ht₁ ht₂ ih₁ ih₂ =>
    obtain ⟨hcf, hce⟩ := Expr.bin_closed_iff.mp hc
    obtain hv₁ | ⟨c', hs⟩ := ih₁ hcf
    · obtain hv₂ | ⟨c', hs⟩ := ih₂ hce
      · exact Or.inl (.pair _ _ hv₁ hv₂)
      · exact Or.inr ⟨_, Step.binR _ _ _ _ _ _ hv₁ hs⟩
    · exact Or.inr ⟨_, Step.binL _ _ _ _ _ _ hs⟩
  | cond c et ef t htc htet htef ihc ihet ihef =>
    right
    obtain ⟨hcc, hcet, hcef⟩ := Expr.cond_closed_iff.mp hc
    obtain hvc | ⟨c', hs⟩ := ihc hcc
    · obtain ⟨_ | _, rfl⟩ := Expr.value_types_bool htc hvc <;>
        repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ _ _ hs⟩
  | proj0 e t₁ t₂ ht ih =>
    right
    have hc := Expr.proj_closed_iff.mp hc
    obtain hv | ⟨c', hs⟩ := ih hc
    · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := Expr.value_types_prod ht hv
      exact ⟨_, Step.proj0 _ _ _ hv₁ hv₂⟩
    · exact ⟨_, Step.proj _ _ _ _ _ hs⟩
  | proj1 e t₁ t₂ ht ih =>
    right
    have hc := Expr.proj_closed_iff.mp hc
    obtain hv | ⟨c', hs⟩ := ih hc
    · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := Expr.value_types_prod ht hv
      exact ⟨_, Step.proj1 _ _ _ hv₁ hv₂⟩
    · exact ⟨_, Step.proj _ _ _ _ _ hs⟩

/--
Reduction preserves types.

This proves the typing conclusions of Theorem 3 from the paper, the rest is
`Computation.preservation_wf`.
-/
theorem Computation.preservation_types {c c' : Computation} {t : Ty}
  (ht : ⊢ c : t) (hs : c ⇒ c') : ⊢ c' : t := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
  | appFn p n e h hv =>
    have .app _ _ t' _ htf hte := ht
    have .fn _ hn := htf
    solve_by_elim [subst_types]
  | appOp p f x y =>
    have .app _ _ t' _ htf hte := ht
    have .const _ := htf
    solve_by_elim
  | appCmp p f x y =>
    have .app _ _ t' _ htf hte := ht
    have .const _ := htf
    solve_by_elim
  | appLogic p f b₁ b₂ =>
    have .app _ _ t' _ htf hte := ht
    have .const _ := htf
    solve_by_elim
  | binL p p' k e₁ e₁' e₂ hs ih =>
    cases ht <;> (
      obtain ⟨htp', ht₁'⟩ := ih htp ‹_›
      constructor
      · exact htp'
      · dsimp only at *
        constructor
        · exact ht₁'
        · exact types_of_step ‹_› hs
    )
  | binR p p' k e₁ e₂ e₂' hv₁ hs ih =>
    cases ht <;> (
      obtain ⟨htp', ht₂'⟩ := ih htp ‹_›
      constructor
      · exact htp'
      · dsimp only at *
        constructor
        · exact types_of_step ‹_› hs
        · exact ht₂'
    )
  | condT p et ef => cases ht; constructor <;> assumption
  | condF p et ef => cases ht; constructor <;> assumption
  | condC p p' c c' et ef hs ih =>
    have .cond _ _ _ _ htc htet htef := ht
    obtain ⟨htp', htc'⟩ := ih htp htc
    constructor
    · exact htp'
    · dsimp only at *
      constructor
      · exact htc'
      · exact types_of_step htet hs
      · exact types_of_step htef hs
  | proj0 p e₁ e₂ hv₁ hv₂ =>
    have .proj0 _ _ t' ht := ht
    have .pair _ _ _ _ ht₁ ht₂ := ht
    solve_by_elim
  | proj1 p e₁ e₂ hv₁ hv₂ =>
    have .proj1 _ _ t' ht := ht
    have .pair _ _ _ _ ht₁ ht₂ := ht
    solve_by_elim
  | proj p p' e e' i hs ih =>
    cases ht <;> (
      simp_all only [forall_const, Fin.isValue]
      obtain ⟨htp', hte'⟩ := ih ‹_›
      solve_by_elim
    )

/--
Reduction preserves well-formedness.

This proves the well-formedness conclusion of Theorem 3 from the paper, the rest
is `Computation.preservation_types`.
-/
theorem Computation.preservation_wf {c c' : Computation} {t : Ty} (ht : ⊢ c : t)
    (hwf : c.WF) (hs : c ⇒ c') : c'.WF := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
    try solve | cases ht <;> apply_rules
  | appFn p n e hn hve =>
    have .app _ _ t' _ htf hte := ht
    exact subst_wf htp.validRefs hte.validRefs hwf
