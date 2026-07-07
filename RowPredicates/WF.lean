module
public import RowPredicates.Pre
public import RowPredicates.Label

@[expose] public section

namespace WF

open Pre Label WF


-- Interdefined Well-formedness rules for Pre.Row and Pre.Ty
mutual
inductive WF_Ty : (inner: Pre.Row) -> Prop where
  | empty : WF_Ty .empty
  | rVar : WF_Ty (.rVar s)
  | extend : WF_Ty r -> Pre.Row.unique_labels r -> r.lack l -> (WF_Row t) -> WF_Ty (.extend r l t)

inductive WF_Row : (inner: Pre.Ty) -> Prop where
  | TVar : WF_Row (.TVar s)
  | TFun : WF_Row arg -> WF_Row ret -> WF_Row (.TFun (arg: Pre.Ty) (ret: Pre.Ty))
  | Singleton : WF_Row (.Singleton l)
  | Pi : WF_Ty r -> WF_Row (.Pi r)
  | Sigma : WF_Ty r -> WF_Row (.Sigma r)
end

-- TODO set up wellfounded induction over Rows and Tys
structure Row : Type where
  inner : Pre.Row
  wf : WF_Ty inner
-- Row must be implemented on top of Pre.Row and bundle well-formedness invariant

structure Ty : Type where
  inner : Pre.Ty
  wf : WF_Row inner

def Row.unique_labels : Row -> Prop
  | .mk inner _ => inner.unique_labels

-- A row lacks a label iff the inner (well-formed) pre-row lacks that label
def Row.lack : Row -> Label -> Prop
  | ⟨inner, _⟩, l => inner.lack l

def Row.has_label : Row -> Label -> Prop
  | ⟨inner, _⟩, l => inner.has_label l

def Row.disjoint : Row -> Row -> Prop
  | ⟨innerL, _⟩, ⟨innerR, _⟩ => innerL.disjoint innerR

def Row.concrete : Row -> Prop
  | ⟨inner, _⟩ => inner.concrete


def Row.type_at_helper (r : Pre.Row) (l : Label) (h : WF_Ty r): Option Ty :=
  match r with
  | .empty => .none
  | .rVar _ => .none
  | .extend r' l' t =>
     if l = l'
      then .some {inner := t, wf := (by cases h ; assumption)}
      else type_at_helper r' l (by cases h ; assumption)

def Row.type_at : Row -> Label -> Option Ty
  | ⟨inner, wf⟩, l => type_at_helper inner l wf


def Row.le (a b : Row) : Prop :=
  a.inner.le b.inner

theorem lacks_extend_lacks {r: Pre.Row} {l1 l2: Label} {t: Pre.Ty} (h_lack: Pre.Row.lack (r.extend l2 t) l1) : Pre.Row.lack r l1 :=
  match h_lack with
  | .extend h' _ => h'

instance : LE Row where
  le := Row.le

theorem Row.le_inner_has_label {r1 r2 : Row} {l : Label } (h_le : r1 ≤ r2) (h_has : r2.inner.has_label l) : r1.inner.has_label l := by
  simp [(.≤.), Row.le, Pre.Row.le] at h_le
  apply (h_le _ h_has).left

theorem Row.le_trans (r1 r2 r3 : Row) (h_1_2 : r1 ≤ r2) (h_2_3 : r2 ≤ r3) : r1 ≤ r3 :=
  λ l h => by
    apply And.intro
    case left =>
      apply le_inner_has_label h_1_2 (le_inner_has_label h_2_3 h)
    case right =>
      simp [(.≤.),Row.le,Pre.Row.le] at *
      grind

theorem Row.le_refl : ∀ (x : Row), x ≤ x :=
  λ _ _ h => And.intro h rfl

instance : Std.IsPreorder Row where
  le_refl := Row.le_refl
  le_trans := Row.le_trans

def Ty.TVar (s : String) : Ty :=
  ⟨Pre.Ty.TVar s, WF_Row.TVar⟩

def Ty.TFun (t1 t2 : Ty) : Ty :=
  ⟨Pre.Ty.TFun t1.inner t2.inner, WF_Row.TFun t1.wf t2.wf⟩

def Ty.Singleton (l : Label) : Ty :=
  {
    inner := Pre.Ty.Singleton l,
    wf := WF_Row.Singleton
  }

def Ty.Pi (r : Row) : Ty :=
  {
    inner := Pre.Ty.Pi r.inner,
    wf := WF_Row.Pi r.wf
  }

def Ty.Sigma (r : Row) : Ty :=
  {
    inner := Pre.Ty.Sigma r.inner,
    wf := WF_Row.Sigma r.wf
  }


mutual

inductive Ty.Equiv : Ty  -> Ty  -> Prop where
  | TVar : Ty.Equiv (Ty.TVar s) (Ty.TVar s)
  | Singleton : Ty.Equiv (Ty.Singleton l) (Ty.Singleton l)
  | Pi : Row.Equiv r1 r2 -> Ty.Equiv (Ty.Pi r1) (Ty.Pi r2)
  | Sigma : Row.Equiv r1 r2 -> Ty.Equiv (Ty.Sigma r1) (Ty.Sigma r2)
  | TFun : Ty.Equiv a1 a2 -> Ty.Equiv r1 r2 -> Ty.Equiv (Ty.TFun a1 r1) (Ty.TFun a2 r2)

inductive Row.Equiv : Row  -> Row  -> Prop where
  | mk {a b : Row} : a ≤ b ∧ b ≤ a -> Row.Equiv a b
end

theorem Row.Equiv.refl : ∀ r: Row, r.Equiv r :=
  λ _ => .mk (And.intro
          (instIsPreorderRow.le_refl _)
          (instIsPreorderRow.le_refl _))

theorem Row.Equiv.symm : ∀ {x y : Row}, x.Equiv y → y.Equiv x :=
  λ h =>
    match h with
    | .mk (And.intro l r) => .mk (And.intro r l)

theorem Row.Equiv.trans : ∀ {x y z: Row}, x.Equiv y → y.Equiv z → x.Equiv z := by
  intro x y z h_x_y h_y_z
  apply Equiv.mk
  apply And.intro <;>
    cases h_x_y <;> cases h_y_z <;>
    simp [.≤.,Row.le,Pre.Row.le] at * <;>
    grind

theorem Ty.Equiv.refl : ∀ x, Ty.Equiv x x :=
  λ x =>
      match x with
      | .TVar _ => .TVar
      | .Singleton _ => .Singleton
      | ⟨.TFun arg ret, WF_Row.TFun wf_a wf_r⟩ =>
        @Equiv.TFun ⟨arg,wf_a⟩ ⟨arg,wf_a⟩ ⟨ret, wf_r⟩ ⟨ret, wf_r⟩ (.refl _) (.refl _)
      | ⟨.Pi r, WF_Row.Pi wf_r⟩ =>
        @Equiv.Pi ⟨r, wf_r⟩ ⟨r, wf_r⟩ (Row.Equiv.refl _)
      | ⟨.Sigma r, WF_Row.Sigma wf_r⟩ =>
        @Equiv.Sigma ⟨r, wf_r⟩ ⟨r, wf_r⟩ (Row.Equiv.refl _)

theorem Ty.Equiv.symm : ∀ {x y : Ty}, x.Equiv y → y.Equiv x :=
  λ h =>
    match h with
    | .TVar => Ty.Equiv.TVar
    | .Singleton => .Singleton
    | .TFun h1 h2 => .TFun (Ty.Equiv.symm h1) (Ty.Equiv.symm h2)
    | .Pi h => .Pi (Row.Equiv.symm h)
    | .Sigma h => .Sigma (Row.Equiv.symm h)

theorem Ty.Equiv.trans : ∀ {x y z : Ty}, x.Equiv y → y.Equiv z → x.Equiv z :=
  @λ x y z h1 h2 =>
    match x, y, z with
    | .TVar x', .TVar y', .TVar z' =>
      by cases h1 ; cases h2; apply Equiv.refl
    | .Singleton x', .Singleton y', .Singleton z' =>
      by cases h1 ; cases h2; apply Equiv.refl
    | ⟨.TFun _ _, _⟩, _, _ =>
        match h1, h2 with
        | @Equiv.TFun ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩ h1a h1r, Equiv.TFun h2a h2r =>
          Equiv.TFun (Ty.Equiv.trans h1a h2a) (Ty.Equiv.trans h1r h2r)
    | ⟨.Pi _, _⟩, _, _ =>
      match h1, h2 with
      | @Equiv.Pi _ ⟨_, _⟩ h_xy, Equiv.Pi h_yz => Ty.Equiv.Pi (Row.Equiv.trans h_xy h_yz)
    | ⟨.Sigma _, _⟩, _, _ =>
      match h1, h2 with
      | @Equiv.Sigma _ ⟨_, _⟩ h_xy, Equiv.Sigma h_yz => Ty.Equiv.Sigma (Row.Equiv.trans h_xy h_yz)

-- This definition of equivalence is syntactic, up to reordering of fields
-- Equivalence of rows with respect to a context or substitution will be defined over quotients of well-formed rows and types
instance : Setoid Ty where
  r := Ty.Equiv
  iseqv := ⟨.refl, .symm, .trans⟩

instance : Setoid Row where
  r := Row.Equiv
  iseqv := ⟨.refl, .symm, .trans⟩
