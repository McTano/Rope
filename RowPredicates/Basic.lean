module

import aesop
public import RowPredicates.Label
public import Std.Data.HashMap.Basic

@[expose] public section

namespace Rope

open Label

-- inductive LabelTerm where
-- | Concrete : String -> LabelTerm
-- | LVar : String -> LabelTerm

-- Start off by just capturing the abstract term syntax
-- without mutual recursion

inductive Term : Type where
  | RVar : (name : String) -> Term
  | TVar : (name : String) -> Term
  | TFun : Term -> Term -> Term
  | Field : Label -> Term -> Term
  | Row : List Term -> Term
  | Singleton : Label -> Term
  | Pi : Term -> Term
  | Sigma : Term -> Term
  -- leaving off type-level functions now to keep it simple
  -- | TApp
  -- | TLam

inductive Kind : Type where
  | KTy : Kind
  | KRow : Kind
  | KLabel : Kind

-- Assert that all fields in the field list have a term which satisfies the given propositional predicate
inductive AllFields : (Pred: Term -> Prop) -> List Term -> Prop where
  | Nil : (AllFields Pred [])
  | Cons : Pred t -> AllFields Pred fields -> (AllFields Pred ((Term.Field l t)::fields))

-- Well-Kindedness Judgement
inductive Term.WK : Term -> Kind -> Prop where
  | RVar : (name : String) -> WK (.RVar name) KRow
  | TVar : (name : String) -> WK (.TVar name) KTy
  | TFun : (Term.WK arg Ty) -> (Term.WK ret Ty) -> (Term.WK (TFun arg ret) Ty)
  -- | Field : (Term.WK t) -> Term
  | Row : (fields: List Term) -> (AllFields (λ t => Term.WK t .KTy) fields) -> (Term.WK (Row fields) KRow)

inductive PredTerm : Type where
  | Leq : Term -> Term -> PredTerm
  | Eq : Term -> Term -> PredTerm
  -- Garrett-style 3-place concatenation predicate
  -- x + y ~ z
  | Concat : Term -> Term -> Term -> PredTerm

inductive PredTerm.WK : PredTerm -> Prop where
  | Leq : Term.WK x KRow -> Term.WK y KRow -> PredTerm.WK (PredTerm.Leq x y)
  | Eq : Term.WK x KRow -> Term.WK y KRow -> Term.WK y KRow -> PredTerm.WK (PredTerm.Concat x y z)
  | Concat : Term.WK x KRow -> Term.WK y KRow -> Term.WK y KRow -> PredTerm.WK (PredTerm.Concat x y z)

mutual
inductive PreRow : Type where
  | empty : PreRow -- (Identity for Concat)
  | rVar : String -> PreRow
  | extend : PreRow -> Label -> PreTy -> PreRow

inductive PreTy : Type where
  | TVar (name : String) : PreTy
  | TFun (arg: PreTy) (ret: PreTy) : PreTy
  | Singleton : Label -> PreTy
  | Pi : PreRow -> PreTy
  | Sigma : PreRow -> PreTy
end

inductive PreRow.lack : PreRow -> (Label) -> Prop where
  | empty : PreRow.lack .empty l
  | rVar : l ≠ l -> PreRow.lack (PreRow.rVar s) l
  | extend : PreRow.lack r l -> l ≠ l' -> PreRow.lack (extend r l' t) l

theorem PreRow.lack_extend_lack : lack (.extend r l' t) l -> lack r l
| .extend h _ => h

inductive PreRow.has_label : PreRow -> Label -> Prop where
  | first : has_label (.extend r l _) l
  | extend : (has_label r l) -> has_label (.extend r _ _) l

theorem PreRow.has_label_neg_lack (h: has_label r l): ¬lack r l :=
  λ hn =>
    match h with
    | .first => match hn with
      | .extend _ _ => by contradiction
    | .extend h' =>  (has_label_neg_lack h' (lack_extend_lack hn))

inductive PreRow.disjoint : PreRow -> PreRow -> Prop where
  | refl : disjoint .empty .empty
  | extend : disjoint r1 r2 -> l1 ≠ l2 -> r1.lack l2 -> r2.lack l1 -> disjoint (.extend r1' l1 t1) (.extend r2' l2 t2)


theorem disjoint_symm {r1 r2 : PreRow} (h: PreRow.disjoint r1 r2) : PreRow.disjoint r2 r1 :=
  match h with
  | .refl => .refl
  | .extend a b c d => by
    apply Rope.PreRow.disjoint.extend
    constructor
    symm
    exact b
    exact .empty
    exact .empty

inductive PreRow.unique_labels : PreRow -> Prop where
  | empty : unique_labels .empty
  | rVar : unique_labels (.rVar s)
  | extend : unique_labels r -> lack r l -> unique_labels (extend r l t)

-- Row is concrete (Has explicit labels and is not a variable)
-- `concrete` is shallow, so it imposes no constraints on structures nested inside the row
inductive PreRow.concrete : PreRow -> Prop where
  | empty : concrete .empty
  | extend : concrete r -> Label.concrete l -> lack r l -> concrete (extend r l t)

-- Interdefined Well-formedness rules for PreRow and PreTy
mutual 
inductive Row.WF : (inner: PreRow) -> Prop where
  | empty : Row.WF .empty
  | rVar : Row.WF (.rVar s)
  | extend : Row.WF r -> PreRow.unique_labels r -> r.lack l -> (Ty.WF t) -> Row.WF (.extend r l t)

inductive Ty.WF : (inner: PreTy) -> Prop where
  | TVar : Ty.WF (.TVar s)
  | TFun : Ty.WF arg -> Ty.WF ret -> Ty.WF (.TFun (arg: PreTy) (ret: PreTy))
  | Singleton : Ty.WF (.Singleton l)
  | Pi : Row.WF r -> Ty.WF (.Pi r)
  | Sigma : Row.WF r -> Ty.WF (.Sigma r)
end

open PreRow Row.WF

-- TODO set up wellfounded induction over Rows and Tys
structure Row : Type where
  inner : PreRow
  wf : Row.WF inner
-- Row must be implemented on top of PreRow and bundle well-formedness invariant

structure Ty : Type where
  inner : PreTy
  wf : Ty.WF inner

-- notation "" => Row.empty
-- notation l " : " t ", " tail => Row.extend tail l t
-- notation "@@" t => Ty.TVar t

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

theorem PreRow.unique_labels_lack_extend : PreRow.unique_labels (.extend r l t) -> PreRow.lack r l := by
  intro h
  cases h
  assumption

theorem PreRow.unique_labels_extend {pr : PreRow} {l t} : PreRow.unique_labels (.extend pr l t) -> PreRow.unique_labels pr := by
  cases pr <;> intro h
  apply unique_labels.empty
  apply unique_labels.rVar

  cases h ;  
  assumption

theorem row_unique_labels : ∀ (r : Row), Row.unique_labels r
  | {inner, wf} => by
    simp [Row.unique_labels] ; cases wf <;> constructor <;> assumption

-- This should (maybe?) bundle evidence eventually
inductive Pred : Type where
  | Leq (x: Row) (y: Row) : Pred
  | Concat (x: Row) (y: Row) (z: Row) :Pred
  | Eq (x: Row) (y: Row) : Pred

def PreRow.type_at (r: PreRow) (l: Label) : Option PreTy :=
  match r with
    | .empty => .none
    | .rVar _ => .none
    | .extend r' l' t =>
        if l = l'
        then .some t
        else type_at r' l


def Row.type_at_helper (r : PreRow) (l : Label) (h : Row.WF r): Option Ty :=
  match r with
  | .empty => .none
  | .rVar _ => .none
  | .extend r' l' t =>
     if l = l'
      then .some {inner := t, wf := (by cases h ; assumption)}
      else type_at_helper r' l (by cases h ; assumption)

def Row.type_at : Row -> Label -> Option Ty
  | ⟨inner, wf⟩, l => type_at_helper inner l wf


def PreRow.le (r1 r2: PreRow) : Prop :=
  forall (l : Label), r2.has_label l -> r1.has_label l ∧ (type_at r1 l) = (type_at r2 l)

def Row.le (a b : Row) : Prop :=
  a.inner.le b.inner

theorem lacks_extend_lacks {r: PreRow} {l1 l2: Label} {t: PreTy} (h_lack: lack (r.extend l2 t) l1) : lack r l1 :=
  match h_lack with
  | .extend h' _ => h'

instance : LE Row where
  le := Row.le

theorem Row.le_inner_has_label {r1 r2 : Row} {l : Label } (h_le : r1 ≤ r2) (h_has : r2.inner.has_label l) : r1.inner.has_label l := by
  simp [(.≤.), Row.le, PreRow.le] at h_le
  apply (h_le _ h_has).left

theorem Row.le_trans (r1 r2 r3 : Row) (h_1_2 : r1 ≤ r2) (h_2_3 : r2 ≤ r3) : r1 ≤ r3 :=
  λ l h => by
    apply And.intro
    case left =>
      apply le_inner_has_label h_1_2 (le_inner_has_label h_2_3 h)
    case right =>
      simp [(.≤.),Row.le,PreRow.le] at *
      grind

theorem Row.le_refl : ∀ (x : Row), x ≤ x :=
  λ _ _ h => And.intro h rfl

instance : Std.IsPreorder Row where
  le_refl := Row.le_refl
  le_trans := Row.le_trans

def Ty.TVar (s : String) : Ty :=
  Ty.mk (PreTy.TVar s) Ty.WF.TVar

def Ty.TFun (t1 t2 : Ty) : Ty :=
  {
    inner := (PreTy.TFun t1.inner t2.inner),
    wf := (Ty.WF.TFun t1.wf t2.wf)
  }

def Ty.Singleton (l : Label) : Ty :=
  {
    inner := PreTy.Singleton l,
    wf := Ty.WF.Singleton
  }

def Ty.Pi (r : Row) : Ty :=
  {
    inner := PreTy.Pi r.inner,
    wf := WF.Pi r.wf
  }

def Ty.Sigma (r : Row) : Ty :=
  {
    inner := PreTy.Sigma r.inner,
    wf := WF.Sigma r.wf
  }

mutual

inductive Ty.Equiv : Ty  -> Ty  -> Prop where
  | TVar : Ty.Equiv (Ty.TVar s) (Ty.TVar s)
  | Singleton : Ty.Equiv (Ty.Singleton l) (Ty.Singleton l)
  | Pi : Row.Equiv r1 r2 -> Ty.Equiv (.Pi r1) (.Pi r2)
  | Sigma : Row.Equiv r1 r2 -> Ty.Equiv (.Sigma r1) (.Sigma r2)
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
    simp [.≤.,Row.le,PreRow.le] at * <;>
    grind

-- theorem refold_ty (inner : PreTy) (wf : Ty.WF inner) : (Ty.mk inner wf) -> Ty :=
--   sorry

theorem Ty.Equiv.refl : ∀ x, Ty.Equiv x x :=
  λ x => 
      match x with
      | .TVar _ => .TVar
      | .Singleton _ => .Singleton
      | ⟨.TFun arg ret, WF.TFun wf_a wf_r⟩ =>
        @Equiv.TFun ⟨arg,wf_a⟩ ⟨arg,wf_a⟩ ⟨ret, wf_r⟩ ⟨ret, wf_r⟩ (.refl _) (.refl _)
      | ⟨.Pi r, WF.Pi wf_r⟩ =>
        @Equiv.Pi ⟨r, wf_r⟩ ⟨r, wf_r⟩ (Row.Equiv.refl _)
      | ⟨.Sigma r, WF.Sigma wf_r⟩ =>
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
    -- match h1, z with
    -- -- | .TFun _ _, .TFun _ _ => sorry
    -- | Equiv.TVar, .TVar _ => Equiv.refl _
    -- | Equiv.Singleton, Equiv.Singleton => Equiv.refl _
    -- | @Equiv.TFun x1 y1 x2 y2 hxy1 hxy2, h2' =>
    --   by
        -- case
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

        
    
  -- intro x y z h_x_y h_y_z
  -- case refl => exact h_y_z
  -- case TVar h_seq =>
  --   cases h_y_z
  --   case refl a =>
  --     rw [h_seq]
  --     exact Equiv.refl
  --   case TVar h_seq' =>
  --     rw [<-h_seq', <- h_seq]
  --     exact .refl
  -- case TFun a1 a2 r1 r2 ha hr =>
  --   case mk z_inner z_wf =>
      
  --   case TFun h1 h2 => exact .refl
  --   case refl a => exact .refl
  -- case Singleton _ => sorry
  -- case Pi h => sorry
  -- case Sigma h => sorry
  -- λ x y z h_x_y h_y_z =>
  --   match h_x_y with
  --   | .refl => h_y_z
  --   | .TVar h => by
  --     rw [h]
  --     apply h_y_z
  --   | .TFun h1 h2 =>
  --     -- | .refl => sorry
  --     -- | ⟨z_inner, z_wf⟩ => by
  --     -- match h_y_z with
  --     -- | .Singleton => sorry
  --     -- | _ => sorry
  --   | .Singleton h => sorry
  --   | .Pi h => sorry
  --   | .Sigma h => sorry

-- -- Defining an equivalence relation parameterized by a value `p`
-- def paramEquiv (p : P) (x y : α) : Prop := sorry

-- -- Proving it forms a Setoid (Equivalence, Symmetry, Transitivity) for each `p`
-- instance (p : P) : Setoid (αWithParam p) where
-- --   iseqv := ...

-- Equality in a context is too complex for the initial definition.
-- Define Family or wrapped type over ty, row, label with context, then define Equiv and Setoid over that.
instance : Setoid Ty where
  r := Ty.Equiv
  iseqv := ⟨.refl, .symm, .trans⟩

instance : Setoid Row where
  r := Row.Equiv 
  iseqv := ⟨.refl, .symm, .trans⟩

def KindType (k : Kind) : Type :=
  match k with
  | .KRow => Row
  | .KTy => Ty
  | .KLabel => Label

def KindContext : Kind -> Type := λ k => Std.HashMap String (KindType k)

def KindContext.empty {k : Kind} : KindContext k := .emptyWithCapacity

structure Context where
  rowContext : KindContext .KRow := .empty
  typeContext : KindContext .KTy := .empty
  labelContext : KindContext .KLabel := .empty
  getContext (k: Kind) : KindContext k :=
      match k with
      | .KRow => rowContext
      | .KTy => typeContext
      | .KLabel => labelContext
  get {k : Kind} (s: String) : Option (KindType k) := (getContext k).get? s
  insert {k : Kind} (s: String) : Option (KindType k) := (getContext k).get? s

def Context.empty : Context := {}

inductive WithContext {c : Context} (T : Type): Type where
| wrap : T -> WithContext T

def unwrap : WithContext (c := c) T -> T
| .wrap x => x

def RowWithContext {c : Context} := WithContext (c := c) Row
def TyWithContext {c : Context} := WithContext (c := c) Ty
def LabelWithContext {c : Context} := WithContext (c := c) Label

