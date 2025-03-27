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

inductive Ty where
  | base
  | arrow (a b : Ty)
deriving Repr, DecidableEq

def TyCtx := Nat → Ty

inductive HasType : TyCtx → Term → Ty → Prop where
  | type_var (Γ : TyCtx) (x : Nat) (A : Ty) : Γ x = A → HasType Γ (.var x) A
  | type_abs (Γ : TyCtx) (t : Term) (A B : Ty) : HasType (A .: Γ) t B → HasType Γ (.abs t) (.arrow A B)
  | type_app (Γ : TyCtx) (t₁ t₂ : Term) (A B : Ty) : HasType Γ t₁ (.arrow A B) → HasType Γ t₂ A → HasType Γ (.app t₁ t₂) B
