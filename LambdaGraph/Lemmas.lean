import LambdaGraph.Basic

theorem app_closed_iff {p : Env} {f e : Expr} :
    (f.app e).Closed p ↔ f.Closed p ∧ e.Closed p := by
  constructor
  · intro h
    constructor <;> solve_by_elim [Free.appL, Free.appR]
  · rintro ⟨hf, he⟩ n (- | -) <;> solve_by_elim

theorem cond_closed_iff {p : Env} {c et ef : Expr} :
    (c.cond et ef).Closed p ↔ c.Closed p ∧ et.Closed p ∧ ef.Closed p := by
  constructor
  · intro h
    and_intros <;> solve_by_elim [Free.condC, Free.condT, Free.condF]
  · rintro ⟨hc, het, hef⟩ n (- | - | -) <;> solve_by_elim

theorem value_types_cn {p : Env} {v : Expr} {t : Ty} (h : p ⊢ v : t.cn) :
    v.Value → ∃ n, v = .fn n
  | .fn n => by simp
  | .bool b => nomatch h

theorem value_types_bool {p : Env} {v : Expr} (h : p ⊢ v : .bool) :
    v.Value → ∃ b, v = .bool b
  | .fn n => nomatch h
  | .bool b => by simp

theorem progress (p : Program) (t : Ty) (ht : ⊢ p : t) (hc : p.Closed) :
    p.expr.Value ∨ ∃ p', p ⇒ p' := by
  obtain ⟨p, e⟩ := p
  obtain ⟨htp, hte⟩ := ht
  simp only [Program.Closed] at *
  induction hte with
  | var n hn => exfalso; exact hc n .var
  | fn n hn => left; constructor
  | app f e t htf hte ihf ihe =>
    right
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    rcases ihf hcf with hvf | ⟨p', hp⟩
    · rcases ihe hce with hve | ⟨p', hp⟩
      · obtain ⟨n, rfl⟩ := value_types_cn htf hvf
        constructor
        constructor
        · cases htf
          assumption
        · exact hve
      · exact ⟨_, Step.appR _ _ _ _ _ hvf hp⟩
    · exact ⟨_, Step.appL _ _ _ _ _ hp⟩
  | bool b => left; constructor
  | cond c et ef t htc htet htef ihc ihet ihef =>
    right
    obtain ⟨hcc, hcet, hcef⟩ := cond_closed_iff.mp hc
    rcases ihc hcc with hvc | ⟨p', hp⟩
    · rcases value_types_bool htc hvc with ⟨_ | _, rfl⟩ <;> repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ _ _ hp⟩
