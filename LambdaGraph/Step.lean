import LambdaGraph.Subst

/-- The small-step reduction relation. -/
inductive Computation.Step : Computation → Computation → Prop where
  | app (p : Program) (n : Nat) (e : Expr) (_ : n < p.size) :
    e.Value → Step ⟨p, .app (.fn n) e⟩ (.subst ⟨p, p.fn[n]⟩ n e)
  | appL (p p' : Program) (f f' e : Expr) :
    Step ⟨p, f⟩ ⟨p', f'⟩ → Step ⟨p, f.app e⟩ ⟨p', f'.app e⟩
  | appR (p p' : Program) (f e e' : Expr) :
    f.Value → Step ⟨p, e⟩ ⟨p', e'⟩ → Step ⟨p, f.app e⟩ ⟨p', f.app e'⟩
  | condT (p : Program) (et ef : Expr) :
    Step ⟨p, (.cond (.bool true) et ef)⟩ ⟨p, et⟩
  | condF (p : Program) (et ef : Expr) :
    Step ⟨p, (.cond (.bool false) et ef)⟩ ⟨p, ef⟩
  | condC (p p' : Program) (c c' et ef : Expr) :
    Step ⟨p, c⟩ ⟨p', c'⟩ → Step ⟨p, c.cond et ef⟩ ⟨p', c'.cond et ef⟩

notation:40 p:41 " ⇒ " p':41 => Computation.Step p p'

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

theorem types_of_step {c c' : Computation} {e : Expr} {t : Ty}
    (ht : c.toProgram ⊢ e : t) (hs : c ⇒ c') : c'.toProgram ⊢ e : t := by
  induction ht with
    (try rw [ty_eq_of_step ‹_› hs]) <;> constructor <;> assumption

theorem progress {c : Computation} {t : Ty} (hte : c.toProgram ⊢ c.expr : t)
    (hc : c.Closed) : c.expr.Value ∨ ∃ c', c ⇒ c' := by
  obtain ⟨p, e⟩ := c
  simp only at *
  induction hte with
  | var n hn => simp [Closed] at hc
  | fn n hn => left; constructor
  | app f e t htf hte ihf ihe =>
    right
    obtain ⟨hcf, hce⟩ := Expr.app_closed_iff.mp hc
    rcases ihf hcf with hvf | ⟨p', hp⟩
    · rcases ihe hce with hve | ⟨p', hp⟩
      · obtain ⟨n, rfl⟩ := value_types_cn htf hvf
        cases htf
        solve_by_elim [Exists.intro]
      · exact ⟨_, Step.appR _ _ _ _ _ hvf hp⟩
    · exact ⟨_, Step.appL _ _ _ _ _ hp⟩
  | bool b => left; constructor
  | cond c et ef t htc htet htef ihc ihet ihef =>
    right
    obtain ⟨hcc, hcet, hcef⟩ := Expr.cond_closed_iff.mp hc
    rcases ihc hcc with hvc | ⟨p', hp⟩
    · rcases value_types_bool htc hvc with ⟨_ | _, rfl⟩ <;> repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ _ _ hp⟩

theorem preservation_types {c c' : Computation} {t : Ty} (ht : ⊢ c : t)
  (hs : c ⇒ c') : ⊢ c' : t := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
  | app p n e h hv =>
    have .app _ _ t htf hte := ht
    cases htf
    solve_by_elim [subst_types]
  | appL p p' f f' e hs ih =>
    have .app _ _ t htf hte := ht
    obtain ⟨htp', htf'⟩ := ih htp htf
    constructor
    · exact htp'
    · dsimp only at *
      constructor
      · exact htf'
      · exact types_of_step hte hs
  | appR p p' f e e' hvf hs ih =>
    have .app _ _ t htf hte := ht
    obtain ⟨htp', hte'⟩ := ih htp hte
    constructor
    · exact htp'
    · dsimp only at *
      constructor
      · exact types_of_step htf hs
      · exact hte'
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

theorem preservation_wf {c c' : Computation} {t : Ty} (ht : ⊢ c : t)
    (hwf : c.WF) (hs : c ⇒ c') : c'.WF := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
    try solve | cases ht <;> apply_rules
  | app p n e hn hve =>
    have .app _ _ t' htf hte := ht
    exact subst_wf htp.validRefs hte.validRefs hwf

end Computation
