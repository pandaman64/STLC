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
theorem scons_comp {α : Type} (v : Nat) (ρ : Rename) (σ : Nat → α) : (v .: ρ) >>> σ = σ v .: (ρ >>> σ) := by
  funext x
  cases x <;> rfl

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

theorem rename_id : rename id = id := by
  funext t
  induction t with
  | var x => rfl
  | abs t ih => simp [rename, up, ih]
  | app t₁ t₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]

@[simp]
theorem Term.rename_rename (ρ₁ ρ₂ : Rename) (t : Term) : rename ρ₂ (rename ρ₁ t) = rename (ρ₁ >>> ρ₂) t := by
  induction t generalizing ρ₁ ρ₂ with
  | var x => simp [rename, comp]
  | abs t ih => simp [rename, ih (up ρ₁) (up ρ₂)]; unfold up; simp;
  | app t₁ t₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]

def Substitution := Nat → Term

def ids : Substitution := .var

def ren (ρ : Rename) : Substitution := ρ >>> ids

theorem ren_def (ρ : Rename) (x : Nat) : ren ρ x = .var (ρ x) := rfl

@[simp]
theorem ids_rename (ρ : Rename) : ids >>> rename ρ = ren ρ := rfl

@[simp]
theorem scons_ren_shift : ids 0 .: ren shift = ids := by
  funext x
  cases x <;> rfl

def Term.subst (σ : Substitution) : Term → Term
  | .var x => σ x
  | .abs t => .abs (t.subst (ids 0 .: (σ >>> rename shift)))
  | .app t₁ t₂ => .app (t₁.subst σ) (t₂.subst σ)

theorem Term.subst_id : subst ids = id := by
  funext t
  induction t with
  | var x => rfl
  | abs t ih => simp [subst, ih]
  | app t₁ t₂ ih₁ ih₂ => simp [subst, ih₁, ih₂]
