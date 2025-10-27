import LambdaGraph.Basic

theorem value_types_cn {L : Type} {p : Program L} {Γ : Set L} {v : Expr L}
  {t : Ty} (ht : p / Γ ⊢ v : t.cn) (hv : v.Value) : ∃ l σ, v = .clos l σ := by
  rcases hv with ⟨l, σ⟩ | b
  · exists l, σ
  · cases ht

theorem value_types_bool {L : Type} {p : Program L} {Γ : Set L} {v : Expr L}
  (ht : p / Γ ⊢ v : .bool) (hv : v.Value) : ∃ b, v = .bool b := by
  rcases hv with ⟨l, σ⟩ | b
  · cases ht
  · exists b

theorem types_in_superset {L : Type} {p : Program L} {Γ Γ' : Set L} {e : Expr L}
  {t : Ty} (h : p / Γ ⊢ e : t) (hs : Γ ⊆ Γ') : p / Γ' ⊢ e : t := by
  induction h generalizing Γ' with try solve | constructor <;> apply_rules
  | fnNew Γ l h ih =>
    apply Types.fnNew
    apply ih
    simp [hs]

theorem types_subst {L : Type} {p : Program L} {Γ : Set L} {e : Expr L} {t : Ty}
  {σ : Env L} (hΓ : ∀ l ∈ Γ, p / Γ ⊢ p.fn l : .bot) (h : p / Γ ⊢ e : t)
  (hσ : ∀ l ∈ Γ, p / ∅ ⊢ σ l : p.ty l) : p / ∅ ⊢ e.subst σ : t := by
  induction h with try solve | (try constructor) <;> apply_rules
  | fnRec Γ l hl =>
    constructor
    · apply types_in_superset (hΓ l hl)
      change Γ ⊆ insert l Γ
      simp
    · exact hΓ
    · exact hσ

theorem progress {L : Type} [DecidableEq L] {p : Program L} {e : Expr L}
  {t : Ty} (h : p / ∅ ⊢ e : t) : e.Value ∨ ∃ e', p / e ⇒ e' := by
  generalize hΓ : (∅ : Set L) = Γ at h
  induction h with subst hΓ
  | var Γ l hl => simp at hl
  | fnRec Γ l hl => simp at hl
  | fnNew Γ l h ih => right; repeat constructor
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

theorem preservation {L : Type} [DecidableEq L] {p : Program L} {e e' : Expr L}
  {t : Ty} (h : p / ∅ ⊢ e : t) (hs : p / e ⇒ e') : p / ∅ ⊢ e' : t := by
  induction hs generalizing t with
    try solve | cases h <;> apply_rules [Types.app, Types.cond]
  | fn l =>
    cases h <;> constructor <;> intros <;> apply_rules [List.not_mem_nil]
  | app l σ e hve =>
    cases h with
    | app _ _ _ t h he =>
      cases h with
      | clos _ Γ _ _ h hΓ hσ =>
        apply types_subst (Γ := insert l Γ)
        · rintro l' (rfl | hl')
          · exact h
          · exact types_in_superset (hΓ l' hl') (by simp)
        · exact h
        · rintro l' (rfl | hl')
          · simp [he, Env.update]
          · simp only [Env.update]
            split <;> subst_eqs <;> apply_rules
