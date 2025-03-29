open Classical

set_option autoImplicit false

inductive Term where
  | var (x : Nat)
  | abs (t : Term)
  | app (t₁ t₂ : Term)
deriving Repr, DecidableEq

def comp {α β γ : Type} (ρ : α → β) (σ : β → γ) : α → γ := fun x => σ (ρ x)

infixl:70 " >>> " => comp

@[simp]
theorem id_comp {α β : Type} (ρ : α → β) : id >>> ρ = ρ := rfl

@[simp]
theorem comp_id {α β : Type} (ρ : α → β) : ρ >>> id = ρ := rfl

@[simp]
theorem comp_assoc {α β γ δ : Type} (σ₁ : α → β) (σ₂ : β → γ) (σ₃ : γ → δ) : (σ₁ >>> σ₂) >>> σ₃ = σ₁ >>> (σ₂ >>> σ₃) := rfl

def scons {α : Type} (t : α) (σ : Nat → α) : Nat → α
  | 0 => t
  | x + 1 => σ x

infixr:60 " .: " => scons

@[simp]
theorem scons_zero {α : Type} (t : α) (σ : Nat → α) : (t .: σ) 0 = t := rfl

@[simp]
theorem scons_succ {α : Type} (t : α) (σ : Nat → α) (x : Nat) : (t .: σ) (x + 1) = σ x := rfl

def Rename := Nat → Nat

@[simp]
theorem scons_comp {α β : Type} (v : α) (ρ : Nat → α) (σ : α → β) : (v .: ρ) >>> σ = σ v .: (ρ >>> σ) := by
  funext x
  cases x <;> rfl

@[simp]
theorem scons_eq_iff {α : Type} {v₁ v₂ : α} {ρ₁ ρ₂ : Nat → α} : v₁ .: ρ₁ = v₂ .: ρ₂ ↔ v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  apply Iff.intro
  . intro h
    refine ⟨?_, ?_⟩
    . have := congrFun h 0
      simpa
    . funext x
      have := congrFun h (x + 1)
      simpa
  . intro h
    simp [h]

def shift : Rename := fun x => x + 1

@[simp]
theorem scons_shift : 0 .: shift = id := by
  funext x
  cases x <;> rfl

@[simp]
theorem shift_scons {α : Type} (t : α) (σ : Nat → α) : shift >>> (t .: σ) = σ := by
  funext x
  cases x <;> rfl

def up (ρ : Rename) : Rename := 0 .: ρ >>> shift

def rename (ρ : Rename) : Term → Term
  | .var x => .var (ρ x)
  | .abs t => .abs (rename (up ρ) t)
  | .app t₁ t₂ => .app (rename ρ t₁) (rename ρ t₂)

@[simp]
theorem rename_var (ρ : Rename) (x : Nat) : rename ρ (.var x) = .var (ρ x) := rfl

@[simp]
theorem rename_abs (ρ : Rename) (t : Term) : rename ρ (.abs t) = .abs (rename (up ρ) t) := rfl

@[simp]
theorem rename_app (ρ : Rename) (t₁ t₂ : Term) : rename ρ (.app t₁ t₂) = .app (rename ρ t₁) (rename ρ t₂) := rfl

@[simp]
theorem rename_id : rename id = id := by
  funext t
  induction t with
  | var x => rfl
  | abs t ih => simp [up, ih]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem rename_rename (ρ₁ ρ₂ : Rename) (t : Term) : rename ρ₂ (rename ρ₁ t) = rename (ρ₁ >>> ρ₂) t := by
  induction t generalizing ρ₁ ρ₂ with
  | var x => simp [comp]
  | abs t ih => simp [up, ih]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem rename_rename' (ρ₁ ρ₂ : Rename) : rename ρ₁ >>> rename ρ₂ = rename (ρ₁ >>> ρ₂) := by
  funext t
  simp [comp]

def Substitution := Nat → Term

def ids : Substitution := .var

def ren (ρ : Rename) : Substitution := ρ >>> ids

theorem ren_def (ρ : Rename) (x : Nat) : ren ρ x = .var (ρ x) := rfl

-- @[simp]
-- theorem ids_rename (ρ : Rename) : ids >>> rename ρ = ren ρ := rfl

@[simp]
theorem ids_rename (ρ : Rename) : ids >>> rename ρ = ρ >>> ids := rfl

@[simp]
theorem rename_ids (ρ : Rename) (v : Nat) : rename ρ (ids v) = ids (ρ v) := rfl

@[simp]
theorem scons_ren_shift : ids 0 .: ren shift = ids := by
  funext x
  cases x <;> rfl

@[simp]
theorem scons_ren_shift' : ids 0 .: ids >>> rename shift = ids := by
  simp [←scons_comp]

@[simp]
theorem ids_shift_ids : ids 0 .: shift >>> ids = ids := by
  simp [←scons_comp]

def subst (σ : Substitution) : Term → Term
  | .var x => σ x
  | .abs t => .abs (subst (ids 0 .: (σ >>> rename shift)) t)
  | .app t₁ t₂ => .app (subst σ t₁) (subst σ t₂)

@[simp]
theorem subst_var (σ : Substitution) (x : Nat) : subst σ (.var x) = σ x := rfl

@[simp]
theorem subst_abs (σ : Substitution) (t : Term) : subst σ (.abs t) = .abs (subst (ids 0 .: (σ >>> rename shift)) t) := rfl

@[simp]
theorem subst_app (σ : Substitution) (t₁ t₂ : Term) : subst σ (.app t₁ t₂) = .app (subst σ t₁) (subst σ t₂) := rfl

@[simp]
theorem subst_ids : subst ids = id := by
  funext t
  induction t with
  | var x => rfl
  | abs t ih => simp [ih]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem ids_subst (σ : Substitution) (x : Nat) : subst σ (ids x) = σ x := rfl

@[simp]
theorem ids_subst' (σ : Substitution) : ids >>> subst σ = σ := by
  funext x
  simp [comp]

theorem rename_subst (ρ : Rename) (t : Term) : rename ρ t = subst (ren ρ) t := by
  induction t generalizing ρ with
  | var x => rfl
  | abs t ih => simp [ren, up, ih]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem rename_subst_comp (ρ : Rename) (σ : Substitution) (t : Term) : subst σ (rename ρ t) = subst (ρ >>> σ) t := by
  induction t generalizing ρ σ with
  | var x => rfl
  | abs t ih => simp [ih, up]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem rename_subst_comp' (ρ : Rename) (σ : Substitution) : rename ρ >>> subst σ = subst (ρ >>> σ) := by
  funext t
  simp [comp]

@[simp]
theorem subst_rename_comp (σ : Substitution) (ρ : Rename) (t : Term) : rename ρ (subst σ t) = subst (σ >>> rename ρ) t := by
  induction t generalizing σ ρ with
  | var x => rfl
  | abs t ih => simp [ih, up]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem subst_rename_comp' (σ : Substitution) (ρ : Rename) : subst σ >>> rename ρ = subst (σ >>> rename ρ) := by
  funext t
  simp [comp]

@[simp]
theorem subst_subst (σ₁ σ₂ : Substitution) (t : Term) : subst σ₂ (subst σ₁ t) = subst (σ₁ >>> subst σ₂) t := by
  induction t generalizing σ₁ σ₂ with
  | var x => rfl
  | abs t ih => simp [ih]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

inductive Step : Term → Term → Prop where
  | step_beta (t u t' : Term) (eq : t' = subst (u .: ids) t) : Step (.app (.abs t) u) t'
  | step_appL (t₁ t₂ u : Term) : Step t₁ t₂ → Step (.app t₁ u) (.app t₂ u)
  | step_appR (t u₁ u₂ : Term) : Step u₁ u₂ → Step (.app t u₁) (.app t u₂)
  | step_abs (t₁ t₂ : Term) : Step t₁ t₂ → Step (.abs t₁) (.abs t₂)

theorem substitutivity {t₁ t₂ : Term} (h : Step t₁ t₂) (σ : Substitution) : Step (subst σ t₁) (subst σ t₂) := by
  induction h generalizing σ with
  | step_beta t u t' eq =>
    subst t'
    refine .step_beta _ _ _ ?_
    -- set_option trace.Meta.Tactic.simp.rewrite true in
    simp -- Wow!
  | step_appL t₁ t₂ u h ih =>
    simp
    exact .step_appL (subst σ t₁) (subst σ t₂) (subst σ u) (ih σ)
  | step_appR t u₁ u₂ h ih =>
    simp
    exact .step_appR (subst σ t) (subst σ u₁) (subst σ u₂) (ih σ)
  | step_abs t₁ t₂ h ih =>
    simp
    let σ' := ids 0 .: σ >>> rename shift
    exact .step_abs (subst σ' t₁) (subst σ' t₂) (ih σ')

theorem step_rename_of_step {t t' : Term} (ρ : Rename) (step : Step t t') : Step (rename ρ t) (rename ρ t') := by
  induction step generalizing ρ with
  | step_beta t u t' eq =>
    subst t'
    simp
    refine .step_beta (rename (up ρ) t) (rename ρ u) (subst (rename ρ u .: ρ >>> ids) t) ?_
    simp [up]
  | step_appL t₁ t₂ u step ih =>
    simp
    exact .step_appL (rename ρ t₁) (rename ρ t₂) (rename ρ u) (ih ρ)
  | step_appR t u₁ u₂ step ih =>
    simp
    exact .step_appR (rename ρ t) (rename ρ u₁) (rename ρ u₂) (ih ρ)
  | step_abs t₁ t₂ step ih =>
    simp
    exact .step_abs (rename (up ρ) t₁) (rename (up ρ) t₂) (ih (up ρ))

inductive Ty where
  | base
  | arrow (a b : Ty)
deriving Repr, DecidableEq

def TyCtx := Nat → Ty

-- Agreement under a renaming. Intuitively, if we take ρ as an injective renaming, then Δ is an extension of Γ.
-- In other words, we can get Δ by weakining and reordering the variables in Γ.
def agrees {α : Type} (Γ Δ : Nat → α) (ρ : Rename) : Prop := Γ = ρ >>> Δ

notation:80 Γ:80 " ⤳[" ρ "] " Δ:80 => agrees Γ Δ ρ

@[simp]
theorem agrees_apply {α : Type} {Γ Δ : Nat → α} {ρ : Rename} (h : Γ ⤳[ρ] Δ) {x : Nat} : Δ (ρ x) = Γ x := by
  unfold agrees at h
  simp [h, comp]

@[simp]
theorem agrees_up_iff {α : Type} {Γ Δ : Nat → α} {ρ : Rename} (A B : α) : (A .: Γ) ⤳[up ρ] (B .: Δ) ↔ A = B ∧ Γ ⤳[ρ] Δ := by
  simp [up, agrees]

@[simp]
theorem agrees_id {α : Type} {Γ : Nat → α} : Γ ⤳[id] Γ := rfl

@[simp]
theorem agrees_shift {α : Type} {Γ : Nat → α} {A : α} : Γ ⤳[shift] (A .: Γ) := by
  funext x
  simp

@[simp]
theorem agrees_comp {α : Type} {Γ₁ Γ₂ Γ₃ : Nat → α} (ρ₁ ρ₂ : Rename) (ag₁ : Γ₁ ⤳[ρ₁] Γ₂) (ag₂ : Γ₂ ⤳[ρ₂] Γ₃) : Γ₁ ⤳[ρ₁ >>> ρ₂] Γ₃ := by
  simp_all [agrees]

inductive HasType : TyCtx → Term → Ty → Prop where
  | type_var (Γ : TyCtx) (x : Nat) (A : Ty) : Γ x = A → HasType Γ (.var x) A
  | type_abs (Γ : TyCtx) (t : Term) (A B : Ty) : HasType (A .: Γ) t B → HasType Γ (.abs t) (.arrow A B)
  | type_app (Γ : TyCtx) (t u : Term) (A B : Ty) : HasType Γ t (.arrow A B) → HasType Γ u A → HasType Γ (.app t u) B

@[simp]
theorem HasType_ids {Γ : TyCtx} {x : Nat} : HasType Γ (ids x) (Γ x) := .type_var Γ x (Γ x) rfl

theorem HasType_rename {Γ Δ : TyCtx} {t : Term} {A : Ty} {ρ : Rename} (ty : HasType Γ t A) (ag : Γ ⤳[ρ] Δ) :
  HasType Δ (rename ρ t) A := by
  induction ty generalizing Δ ρ with
  | type_var Γ x A h =>
    simp
    exact .type_var Δ (ρ x) A (by simp [agrees_apply ag, h])
  | type_abs Γ t A B ty ih =>
    simp
    exact .type_abs Δ (rename (up ρ) t) A B (ih (by simp [ag]))
  | type_app Γ t u A B tyt tyu iht ihu => exact .type_app Δ (rename ρ t) (rename ρ u) A B (iht ag) (ihu ag)

theorem HasType_subst {Γ Δ : TyCtx} {t : Term} {A : Ty} {σ : Substitution} (ty : HasType Γ t A) (ag : ∀ x, HasType Δ (σ x) (Γ x)) :
  HasType Δ (subst σ t) A := by
  induction ty generalizing Δ σ with
  | type_var Γ x A h => simp [←h, ag]
  | type_abs Γ t A B ty ih =>
    simp
    refine .type_abs Δ (subst (ids 0 .: σ >>> rename shift) t) A B (ih ?_)
    intro x
    cases x with
    | zero =>
      simp
      exact .type_var (A .: Δ) 0 A (by simp)
    | succ x =>
      simp [comp]
      exact HasType_rename (ag x) (by simp)
  | type_app Γ t u A B tyt tyu iht ihu =>
    simp
    exact .type_app Δ (subst σ t) (subst σ u) A B (iht ag) (ihu ag)

theorem preservation {Γ : TyCtx} {t t' : Term} {A : Ty} (step : Step t t') (ty : HasType Γ t A) : HasType Γ t' A := by
  induction ty generalizing t' with
  | type_var Γ x A h => nomatch step
  | type_abs Γ t A B ty ih =>
    cases step with
    | step_abs _ t' step => exact .type_abs Γ t' A B (ih step)
  | type_app Γ t u A B tyt tyu iht ihu =>
    cases step with
    | step_beta t _ _ eq =>
      subst t'
      cases tyt with
      | type_abs Γ t A B tyt =>
        apply HasType_subst tyt
        intro x
        cases x with
        | zero => simp [tyu]
        | succ x => simp
    | step_appL _ t₂ _ step => exact .type_app Γ t₂ u A B (iht step) tyu
    | step_appR _ _ u₂ step => exact .type_app Γ t u₂ A B tyt (ihu step)

inductive Steps : Term → Term → Prop
  | refl (t : Term) : Steps t t
  | next (t₁ t₂ t₃ : Term) (step : Step t₁ t₂) (rest : Steps t₂ t₃) : Steps t₁ t₃

theorem preservation_steps {Γ : TyCtx} {t t' : Term} {A : Ty} (steps : Steps t t') (ty : HasType Γ t A) : HasType Γ t' A := by
  induction steps with
  | refl => exact ty
  | next t₁ t₂ t₃ step rest ih => exact ih (preservation step ty)

theorem rename_abs_inv {t u : Term} {ρ : Rename} (eq : rename ρ t = .abs u) : ∃ t', t = .abs t' ∧ rename (up ρ) t' = u := by
  cases t with
  | var | app => simp at eq
  | abs t' =>
    simp at eq
    exact ⟨t', rfl, eq⟩

theorem rename_step_of_step_rename {t₁ t₂ : Term} {ρ : Rename} (step : Step (rename ρ t₁) t₂) : ∃ t₂', rename ρ t₂' = t₂ ∧ Step t₁ t₂' := by
  induction t₁ generalizing ρ t₂ with
  | var x =>
    simp at step
    nomatch step
  | abs t₁ ih =>
    simp at step
    cases step with
    | step_abs _ t₂ step =>
      have ⟨t₂', eq, step'⟩ := ih step
      exact ⟨.abs t₂', by simp [eq], .step_abs _ _ step'⟩
  | app t₁ u ih₁ ih₂ =>
    simp at step
    generalize h : rename ρ t₁ = t₁' at step
    cases step with
    | step_beta s _ _ eq =>
      subst t₂
      have ⟨t₁', eq', rename_eq⟩ := rename_abs_inv h
      subst t₁ s
      exact ⟨subst (u .: ids) t₁', by simp [up], .step_beta t₁' u _ rfl⟩
    | step_appL t₁' t₂ _ step =>
      subst t₁'
      have ⟨t₂', eq, step'⟩ := ih₁ step
      subst t₂
      exact ⟨.app t₂' u, by simp, .step_appL _ _ _ step'⟩
    | step_appR t₁ u u' step =>
      subst t₁'
      have ⟨u'', eq, step'⟩ := ih₂ step
      subst u'
      exact ⟨.app t₁ u'', by simp, .step_appR _ _ _ step'⟩

mutual

inductive Neutral : Term → Prop where
  | ne_var (x : Nat) : Neutral (.var x)
  | ne_app (t u : Term) : Neutral t → Normal u → Neutral (.app t u)

inductive Normal : Term → Prop where
  | no_ne (t : Term) : Neutral t → Normal t
  | no_abs (t : Term) : Normal t → Normal (.abs t)

end

mutual

theorem no_step_of_neutral {t t' : Term} (ne : Neutral t) (step : Step t t') : False := by
  cases ne with
  | ne_var x => nomatch step
  | ne_app t u ne no =>
    cases step with
    | step_beta t _ _ eq => nomatch ne
    | step_appL _ t' _ step => exact no_step_of_neutral ne step
    | step_appR _ _ u' step => exact no_step_of_normal no step

theorem no_step_of_normal {t t' : Term} (no : Normal t) (step : Step t t') : False := by
  cases no with
  | no_ne t ne => exact no_step_of_neutral ne step
  | no_abs t no =>
    cases step with
    | step_abs _ t' step => exact no_step_of_normal no step

end

def Term.isAbs : Term → Bool
  | .abs _ => true
  | .var _ | .app _ _ => false

@[simp]
theorem isAbs_abs {t : Term} : (Term.abs t).isAbs = true := rfl

@[simp]
theorem isAbs_var {x : Nat} : (Term.var x).isAbs = false := rfl

@[simp]
theorem isAbs_app {t₁ t₂ : Term} : (Term.app t₁ t₂).isAbs = false := rfl

theorem normal_or_neutral_of_no_step {t : Term} (step : ∀ t', ¬Step t t') : if t.isAbs then Normal t else Neutral t := by
  induction t with
  | var x =>
    simp
    exact .ne_var x
  | abs t ih =>
    simp
    have h (t' : Term) (step' : Step t t') : False := step (.abs t') (.step_abs t t' step')
    have no : Normal t := by
      have := ih h
      split at this
      next => exact this
      next => exact .no_ne _ this
    exact .no_abs t no
  | app t₁ t₂ ih₁ ih₂ =>
    simp
    refine .ne_app t₁ t₂ ?_ ?_
    . if step' : ∃ t₁', Step t₁ t₁' then
        have ⟨t₁', step'⟩ := step'
        exact False.elim (step (.app t₁' t₂) (.step_appL t₁ t₁' t₂ step'))
      else
        simp at step'
        have ih₁ := ih₁ step'
        match t₁ with
        | .abs t₁ => exact False.elim (step _ (.step_beta t₁ t₂ _ rfl))
        | .var _ | .app _ _ => exact ih₁
    . if step' : ∃ t₂', Step t₂ t₂' then
        have ⟨t₂', step'⟩ := step'
        exact False.elim (step (.app t₁ t₂') (.step_appR t₁ t₂ t₂' step'))
      else
        simp at step'
        have ih₂ := ih₂ step'
        split at ih₂
        next => exact ih₂
        next => exact .no_ne _ ih₂

theorem progress {Γ : TyCtx} {t : Term} {A : Ty} (ty : HasType Γ t A) : Normal t ∨ ∃ t', Step t t' := by
  induction ty with
  | type_var Γ x A h => exact .inl (.no_ne (.var x) (.ne_var x))
  | type_abs Γ t A B ty ih =>
    match ih with
    | .inl no => exact .inl (.no_abs t no)
    | .inr ⟨t', step⟩ => exact .inr ⟨.abs t', .step_abs t t' step⟩
  | type_app Γ t u A B tyt tyu iht ihu =>
    match iht with
    | .inl no₁ =>
      match ihu with
      | .inl no₂ =>
        cases no₁ with
        | no_ne t ne => .exact .inl (.no_ne (.app t u) (.ne_app t u ne no₂))
        | no_abs t no₁ => exact .inr ⟨subst (u .: ids) t, .step_beta t u _ rfl⟩
      | .inr ⟨u', step⟩ => exact .inr ⟨.app t u', .step_appR t u u' step⟩
    | .inr ⟨t', step⟩ => exact .inr ⟨.app t' u, .step_appL t t' u step⟩

inductive SN : Term → Prop where
  | intro (t : Term) (ih : ∀ t', Step t t' → SN t') : SN t

theorem SN_step {t t' : Term} (step : Step t t') (sn : SN t) : SN t' := by
  cases sn with
  | intro _ h => exact h t' step

theorem SN_steps {t t' : Term} (steps : Steps t t') (sn : SN t) : SN t' := by
  induction steps with
  | refl => exact sn
  | next t₁ t₂ t₃ step rest ih => exact ih (SN_step step sn)

theorem SN_of_SN_app {t u : Term} (sn : SN (.app t u)) : SN t ∧ SN u := by
  generalize h : Term.app t u = s at sn
  induction sn generalizing t u with
  | intro t'' _ ih =>
    subst t''
    refine ⟨.intro t fun t' step => ?_, .intro u fun u' step => ?_⟩
    . exact (ih (.app t' u) (.step_appL t t' u step) rfl).1
    . exact (ih (.app t u') (.step_appR t u u' step) rfl).2

theorem SN_of_SN_rename {t : Term} {ρ : Rename} (sn : SN (rename ρ t)) : SN t := by
  generalize h : rename ρ t = s at sn
  induction sn generalizing t ρ with
  | intro t' h ih =>
    subst t'
    refine .intro t (fun t' step => ?_)
    exact ih (rename ρ t') (step_rename_of_step ρ step) rfl

theorem SN_rename_of_SN {t : Term} {ρ : Rename} (sn : SN t) : SN (rename ρ t) := by
  induction sn with
  | intro t h ih =>
    refine .intro (rename ρ t) (fun t' step => ?_)
    have ⟨t'', eq, step'⟩ := rename_step_of_step_rename step
    subst t'
    exact ih t'' step'

def Red (Γ : TyCtx) (t : Term) (A : Ty) : Prop :=
  match A with
  | .base => HasType Γ t .base ∧ SN t
  | .arrow A B => HasType Γ t (.arrow A B) ∧ ∀ ρ Δ u, Γ ⤳[ρ] Δ → Red Δ u A → Red Δ (.app (rename ρ t) u) B

theorem HasType_of_Red {Γ : TyCtx} {t : Term} {A : Ty} (red : Red Γ t A) : HasType Γ t A := by
  cases A with
  | base => simp_all [Red]
  | arrow A B => simp_all [Red]

theorem Red_step {Γ : TyCtx} {t t' : Term} {A : Ty} (red : Red Γ t A) (step : Step t t') : Red Γ t' A := by
  induction A generalizing Γ t t' with
  | base =>
    simp [Red] at *
    exact ⟨preservation step red.1, SN_step step red.2⟩
  | arrow A B ih₁ ih₂ =>
    simp [Red] at *
    refine ⟨preservation step red.1, ?_⟩
    intro ρ Δ u ag red'
    have red'' := red.2 ρ Δ u ag red'
    exact ih₂ red'' (.step_appL (rename ρ t) (rename ρ t') u (step_rename_of_step ρ step))

theorem CN₂ {Γ : TyCtx} {t t' : Term} {A : Ty} (red : Red Γ t A) (steps : Steps t t') : Red Γ t' A := by
  induction steps with
  | refl => exact red
  | next t₁ t₂ t₃ step rest ih => exact ih (Red_step red step)

theorem CN₁₃ {Γ : TyCtx} {t : Term} {A : Ty} : (Red Γ t A → SN t) ∧ (HasType Γ t A → ¬t.isAbs → (∀ t', Step t t' → Red Γ t' A) → Red Γ t A) := by
  induction A generalizing Γ t with
  | base =>
    refine ⟨?_, ?_⟩
    . simp [Red]
    . intro ty ne cls
      simp [Red, ty]
      simp [Red] at cls
      exact .intro t (fun t' step => (cls t' step).2)
  | arrow A B ihA ihB =>
    refine ⟨?_, ?_⟩
    . simp [Red]
      intro ty arg
      have (t' : Term) : ¬Step (.var 0) t' := no_step_of_neutral (t' := t') (.ne_var 0)
      have : Red (A .: Γ) (.var 0) A := ihA.2 (.type_var _ _ _ rfl) (by simp) (by simp [this])
      have : Red (A .: Γ) ((rename shift t).app (.var 0)) B := arg shift (A .: Γ) (.var 0) (by simp) this
      have : SN ((rename shift t).app (.var 0)) := ihB.1 this
      exact SN_of_SN_rename (SN_of_SN_app this).1
    . intro ty ne cls
      refine ⟨ty, fun ρ Δ u ag red => ?_⟩
      have snu : SN u := ihA.1 red

      induction snu with
      | intro u h ih =>
        refine ihB.2 ?_ (by simp) ?_
        . have : HasType Δ (rename ρ t) (.arrow A B) := HasType_rename ty ag
          exact .type_app Δ (rename ρ t) u A B this (HasType_of_Red red)
        . intro t' step
          generalize h : rename ρ t = ρt at step
          cases step with
          | step_beta ρt u u' eq =>
            match t with
            | .abs t => simp at ne
            | .var _ | .app _ _ => simp at h
          | step_appL ρt ρt' u step =>
            subst ρt
            have ⟨t', eq, step'⟩ := rename_step_of_step_rename step
            subst ρt'
            have red' : Red Γ t' (.arrow A B) := cls t' step'
            simp [Red] at red'
            exact red'.2 ρ Δ u ag red
          | step_appR ρt u u' step =>
            subst ρt
            exact ih u' step (Red_step red step)

theorem CN₁ {Γ : TyCtx} {t : Term} {A : Ty} (red : Red Γ t A) : SN t := CN₁₃.1 red

-- This "Neutrality" comes from Girard's "Proofs and Types" and is different from the Neutral above.
theorem CN₃ {Γ : TyCtx} {t : Term} {A : Ty} (ty : HasType Γ t A) (ne : ¬t.isAbs) (cls : ∀ t', Step t t' → Red Γ t' A) : Red Γ t A :=
  CN₁₃.2 ty ne cls

theorem red_rename_of_red_ag {Γ Δ : TyCtx} {t : Term} {A : Ty} {ρ : Rename} (red : Red Γ t A) (ag : Γ ⤳[ρ] Δ) : Red Δ (rename ρ t) A := by
  induction A generalizing Γ Δ t ρ with
  | base =>
    simp [Red] at *
    exact ⟨HasType_rename red.1 ag, SN_rename_of_SN red.2⟩
  | arrow A B ihA ihB =>
    simp [Red] at *
    refine ⟨HasType_rename red.1 ag, ?_⟩
    intro ρ' Δ' u ag' red'
    exact red.2 (ρ >>> ρ') Δ' u (agrees_comp ρ ρ' ag ag') red'
