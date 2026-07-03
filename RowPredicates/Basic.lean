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
  | Pi : PreRow -> Row.WF r -> Ty.WF (.Pi r)
  | Sigma : PreRow -> Row.WF r -> Ty.WF (.Sigma r)
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
    -- 
    | .rVar _ => .none
    | .extend r' l' t =>
      if (l = l')
      then .some t
      else type_at r' l

def Row.type_at_helper (r : PreRow) (l : Label) (h : Row.WF r): Option Ty :=
  match r with
  | .empty => .none
  | .rVar _ => .none
  | .extend r' l' t =>
     if (l = l')
      then .some {inner := t, wf := (by cases h ; assumption)}
      else type_at_helper r' l (by cases h ; assumption)

def Row.type_at : Row -> Label -> Option Ty
  | ⟨inner, wf⟩, l => type_at_helper inner l wf


def PreRow.le (r1 r2: PreRow) : Prop :=
  forall (l1 : Label), (type_at r1 l1) = (type_at r2 l1)

def Row.le (a b : Row) : Prop :=
  a.inner.le b.inner

theorem lacks_extend_lacks {r: PreRow} {l1 l2: Label} {t: PreTy} (h_lack: lack (r.extend l2 t) l1) : lack r l1 :=
  match h_lack with
  | .extend h' _ => h'

instance : LE Row where
  le := Row.le

theorem Row.contained_in_trans {r1 r2 r3 : Row} (h_1_2: le r1 r2) (h_2_3: le r2 r3): le r1 r3 := by
  intro l;
  rw [h_1_2, h_2_3]

instance : Std.IsPreorder Row where
  le_refl := λ x =>
    by intro l
       rfl
  le_trans := λ _ _ _ => Row.contained_in_trans

def Row.equiv_helper (e : Context × Ty -> Context × Ty -> Prop) (c: Context) (a b: Row) (l : Label)
   := (ha : ((Option.isSome (a.type_at l)) = true)) ->
      (hb : (Option.isSome (b.type_at l)) = true) ->
            ((e (c, (a.type_at l).get ha) (c, (b.type_at l).get hb)))

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

def Ty.TVar (s : String) : Ty :=
  Ty.mk (PreTy.TVar s) Ty.WF.TVar

mutual
-- TODO incorporate Variable Lookup into Var Equality
inductive VarEquiv : (p1 p2 : Context × String) -> Prop where
| refl : VarEquiv p1 p2
-- | lookup

inductive Ty.Equiv : Context × Ty -> Context × Ty -> Prop where
  | TVar : VarEquiv (c1, s1) (c2,s2) -> Ty.Equiv (c1, (Ty.TVar s1)) (c1, Ty.TVar p2)
  -- | TFun :
  -- | Singleton : Ty.WF (.Singleton l)
  -- | Pi : PreRow -> Row.WF r -> Ty.WF (.Pi r)
  -- | Sigma : PreRow -> Row.WF r -> Ty.WF (.Sigma r)

inductive Row.Equiv : Row -> Row -> Prop where
  -- | lack a b
  | mk {a b : Row} :
    (∀ (l: Label), 
        (a.lack l = b.lack l)
      -> (Option.isSome (a.type_at l) = Option.isSome (b.type_at l)))
      -> Row.equiv_helper Ty.Equiv .empty a b l -> Row.Equiv a b
end

-- -- Defining an equivalence relation parameterized by a value `p`
-- def paramEquiv (p : P) (x y : α) : Prop := sorry

-- -- Proving it forms a Setoid (Equivalence, Symmetry, Transitivity) for each `p`
-- instance (p : P) : Setoid (αWithParam p) where
--   iseqv := ...

-- Define Family or wrapped type over ty and row with context.
instance : Setoid Ty where
  r := λ a b => sorry
  iseqv := sorry

instance : Setoid (Row) where
  r := Row.Equiv
  iseqv := sorry
