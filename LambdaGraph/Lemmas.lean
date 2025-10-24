import LambdaGraph.Basic

theorem value_types_cn {L : Type} {p : Program L} {Γ : List L} {v : Expr L}
  {t : Ty} (ht : p / Γ ⊢ v : t.cn) (hv : v.Value) : ∃ l σ, v = .clos l σ := by
  rcases hv with ⟨l, σ⟩ | b
  · exists l, σ
  · cases ht

theorem value_types_bool {L : Type} {p : Program L} {Γ : List L} {v : Expr L}
  (ht : p / Γ ⊢ v : .bool) (hv : v.Value) : ∃ b, v = .bool b := by
  rcases hv with ⟨l, σ⟩ | b
  · cases ht
  · exists b

theorem progress {L : Type} [DecidableEq L] {p : Program L} {e : Expr L}
  {t : Ty} (h : p / [] ⊢ e : t) : e.Value ∨ ∃ e', p / e ⇒ e' := by
  generalize hΓ : [] = Γ at h
  induction h with subst hΓ
  | var Γ l hl => simp at hl
  | fnRec Γ l hl => simp at hl
  | fnNew Γ l hl h ih => right; repeat constructor
  | app Γ f e t hf he ihf ihe =>
    right
    rcases ihf rfl with hvf | ⟨f', hsf⟩
    · rcases ihe rfl with hve | ⟨e', hse⟩
      · obtain ⟨l, σ, rfl⟩ := value_types_cn hf hvf
        exact ⟨_, Step.app _ _ _ hve⟩
      · exact ⟨_, Step.appR _ _ _ hvf hse⟩
    · exact ⟨_, Step.appL _ _ _ hsf⟩
  | clos Γ l σ h ih => left; constructor
  | bool Γ b => left; constructor
  | cond Γ c et ef t hc het hef ihc ihet ihef =>
    right
    rcases ihc rfl with hvc | ⟨c', hsc⟩
    · obtain ⟨b, rfl⟩ := value_types_bool hc hvc
      cases b <;> repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ hsc⟩
