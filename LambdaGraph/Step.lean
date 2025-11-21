import LambdaGraph.Subst

/-- The small-step reduction relation. -/
inductive Step : Computation → Computation → Prop where
  | app (p : Program) (n : Nat) (e : Expr) (_ : n < p.size) :
    e.Value → Step ⟨p, .app (.fn n) e⟩ (Computation.subst ⟨p, p.fn[n]⟩ n e)
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

notation:40 p:41 " ⇒ " p':41 => Step p p'

/-- The reflexive-transitive closure of the reduction relation. -/
inductive Steps : Computation → Computation → Prop where
  | refl (p : Computation) : Steps p p
  | step (p p' p'' : Computation) : Step p p' → Steps p' p'' → Steps p p''

notation:40 p:41 " ⇒* " p':41 => Steps p p'

theorem size_le_of_step {p p' : Computation} (h : p ⇒ p') :
    p.size ≤ p'.size := by
  induction h with simp [*, Program.subst, Computation.subst]

theorem lt_size_of_step {p p' : Computation} {n : Nat} (hn : n < p.size)
    (h : p ⇒ p') : n < p'.size := Nat.lt_of_lt_of_le hn (size_le_of_step h)

theorem fn_eq_of_step {p p' : Computation} {n : Nat} (hn : n < p.size)
    (h : p ⇒ p') : p.fn[n] = p'.fn[n]'(lt_size_of_step hn h) := by
  induction h with simp [*, Program.subst, Computation.subst]

theorem ty_eq_of_step {p p' : Computation} {n : Nat} (hn : n < p.size)
    (h : p ⇒ p') : p.ty[n] = p'.ty[n]'(lt_size_of_step hn h) := by
  induction h with simp [*, Program.subst, Computation.subst]

theorem types_of_step {p p' : Computation} {e : Expr} {t : Ty}
    (ht : p.toProgram ⊢ e : t) (hs : p ⇒ p') : p'.toProgram ⊢ e : t := by
  induction ht with
    (try rw [ty_eq_of_step ‹_› hs]) <;> constructor <;> assumption

theorem closed_of_step {p p' : Computation} {e : Expr} (hp : p.ValidRefs)
    (he : e.ValidRefs p.toProgram) (hc : e.Closed p.toProgram) (hs : p ⇒ p') :
    e.Closed p'.toProgram := by
  intro m hf
  apply hc m
  induction hs with
    dsimp only at * <;> apply_rules
  | app =>
    dsimp only [Computation.subst] at *
    exact free_of_free_in_subst hp he hf

theorem progress {p : Computation} {t : Ty} (ht : ⊢ p : t) (hc : p.Closed) :
    p.expr.Value ∨ ∃ p', p ⇒ p' := by
  obtain ⟨p, e⟩ := p
  obtain ⟨htp, hte⟩ := ht
  simp only at *
  induction hte with
  | var n hn => exfalso; exact hc n .var
  | fn n hn => left; constructor
  | app f e t htf hte ihf ihe =>
    right
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
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
    obtain ⟨hcc, hcet, hcef⟩ := cond_closed_iff.mp hc
    rcases ihc hcc with hvc | ⟨p', hp⟩
    · rcases value_types_bool htc hvc with ⟨_ | _, rfl⟩ <;> repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ _ _ hp⟩

theorem preservation_types {p p' : Computation} {t : Ty} (ht : ⊢ p : t)
  (hs : p ⇒ p') : ⊢ p' : t := by
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

theorem preservation_closed {p p' : Computation} {t : Ty} (ht : ⊢ p : t)
    (hc : p.Closed) (hs : p ⇒ p') : p'.Closed := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
  | app p n e hn hve =>
    intro m hm
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    have .app _ _ t' htf hte := ht
    have hmap : (p.labelMap n).Valid n := labelMap_valid _ hn
    have hp : p.ValidRefs := htp.validRefs
    have hfn := hp hn
    have he := hte.validRefs
    have hne : n ≠ m := by
      intro rfl
      simp [Computation.subst, Computation.Free] at hm
      exact not_free_in_subst hmap hp hfn he hce hve hm
    obtain ⟨⟨i, hi⟩, rfl, hf⟩ :=
      eq_map_of_free_in_subst hmap hp hfn he hce hve hm
    simp only [Fin.getElem_fin] at hne
    simp only at hf
    have hd : ¬Nests p n n := by
      intro hd
      obtain ⟨m, hm, hf⟩ := nests_self hd
      exact hcf m (.fn _ _ hm hf)
    have hne : i ≠ n := by
      intro rfl
      simp [hmap.not_nests hi hd] at hne
    exact hcf i (.fn _ hn hne hf)
  | appL p p' f f' e hs ih =>
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    apply app_closed_iff.mpr
    have .app _ _ t' htf hte := ht
    dsimp only at *
    constructor
    · exact ih hcf htp htf
    · exact closed_of_step htp.validRefs hte.validRefs hce hs
  | appR p p' f e e' hvf hs ih =>
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    apply app_closed_iff.mpr
    have .app _ _ t' htf hte := ht
    dsimp only at *
    constructor
    · exact closed_of_step htp.validRefs htf.validRefs hcf hs
    · exact ih hce htp hte
  | condT p et ef =>
    obtain ⟨-, hcet, -⟩ := cond_closed_iff.mp hc
    exact hcet
  | condF p et ef =>
    obtain ⟨-, -, hcef⟩ := cond_closed_iff.mp hc
    exact hcef
  | condC p p' c c' et ef hs ih =>
    obtain ⟨hcc, hcet, hcef⟩ := cond_closed_iff.mp hc
    apply cond_closed_iff.mpr
    have .cond _ _ _ _ htc htet htef := ht
    and_intros
    · exact ih hcc htp htc
    · apply closed_of_step htp.validRefs htet.validRefs hcet
      exact (.condC _ _ _ _ _ _ hs)
    · apply closed_of_step htp.validRefs htef.validRefs hcef
      exact (.condC _ _ _ _ _ _ hs)
