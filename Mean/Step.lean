import Mean.Subst

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

theorem fn_eq_of_step {c c' : Computation} (h : c ⇒ c') {n : Nat}
    (hn : n < c.size) : c'.fn[n]'(lt_size_of_step hn h) = c.fn[n] := by
  induction h with simp [subst, Program.subst_fn_eq_of_lt hn, *]

theorem ty_eq_of_step {c c' : Computation} (h : c ⇒ c') {n : Nat}
    (hn : n < c.size) : c'.ty[n]'(lt_size_of_step hn h) = c.ty[n] := by
  induction h with simp [subst, Program.subst_ty_eq_of_lt hn, *]

theorem ret_eq_of_step {c c' : Computation} (h : c ⇒ c') {n : Nat}
    (hn : n < c.size) : c'.ret[n]'(lt_size_of_step hn h) = c.ret[n] := by
  induction h with simp [subst, Program.subst_ret_eq_of_lt hn, *]

@[grind →]
theorem prefix_of_step {c c' : Computation} (h : c ⇒ c') :
    c.Prefix c'.toProgram := by
  constructor
  · exact fn_eq_of_step h
  · exact ty_eq_of_step h
  · exact ret_eq_of_step h
  · exact size_le_of_step h

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

theorem Computation.free_of_step_of_free {c c' : Computation} {t : Ty} {n : Nat}
    (ht : ⊢ c : t) (hwf : c.WF) (hs : c ⇒ c') (hf : c'.Free n) : c.Free n := by
  obtain ⟨htp, hte⟩ := ht
  induction hs generalizing t with try grind [Free, cases BinKind]
  | appFn p m e hm he =>
    replace .app _ _ t' _ htf hte := hte
    dsimp only [Free] at *
    have h : ∀ k, p.fn[m].Free p k → k ≽[p] m := by
      intro k hf
      by_cases k = m
      · subst k
        exact .refl hm
      · exact .nests _ (.free _ _ (by grind) hm ‹_› hf)
    obtain ⟨hf, hne⟩ | h :=
      free_of_free_in_subst htp.validRefs (htp.validRefs hm) hte.validRefs hwf h hf
    · exact .binL _ _ _ (.fn _ hm hne hf)
    · exact .binR _ _ _ h

theorem Computation.preservation_closed {c c' : Computation} {t : Ty}
    (ht : ⊢ c : t) (hwf : c.WF) (hc : c.Closed) (hs : c ⇒ c') : c'.Closed :=
  fun _ hf => hc (free_of_step_of_free ht hwf hs hf)

theorem Computation.preservation_types {c c' : Computation} {t : Ty}
  (ht : ⊢ c : t) (hs : c ⇒ c') : ⊢ c' : t := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with try grind [Types, cases BinKind]
  | appFn p n e h hv =>
    have .app _ _ t _ htf hte := ht
    cases htf
    solve_by_elim [subst_types]

theorem Computation.preservation_wf {c c' : Computation} {t : Ty} (ht : ⊢ c : t)
    (hwf : c.WF) (hs : c ⇒ c') : c'.WF := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with grind [subst_wf, cases BinKind]

/--
Reduction preserves types and well-formedness.

Corresponds to Theorem 3 in the paper.
-/
theorem Computation.preservation {c c' : Computation} {t : Ty} (ht : ⊢ c : t)
    (hwf : c.WF) (hs : c ⇒ c') : ⊢ c' : t ∧ c'.WF :=
  ⟨preservation_types ht hs, preservation_wf ht hwf hs⟩

theorem Computation.preservation_closed_steps {c c' : Computation} {t : Ty}
    (ht : ⊢ c : t) (hwf : c.WF) (hs : c ⇒* c') (hc : c.Closed) : c'.Closed := by
  induction hs with grind [preservation, preservation_closed]

theorem Computation.preservation_steps {c c' : Computation} {t : Ty}
    (ht : ⊢ c : t) (hwf : c.WF) (hs : c ⇒* c') : ⊢ c' : t ∧ c'.WF := by
  induction hs with grind [preservation]

theorem Computation.soundness {c c' : Computation} {t : Ty} (ht : ⊢ c : t)
    (hwf : c.WF) (hc : c.Closed) (hs : c ⇒* c') :
    c'.expr.Value ∨ ∃ c'', c' ⇒ c'' :=
  progress (preservation_steps ht hwf hs).1.expr_types
    (preservation_closed_steps ht hwf hs hc)
