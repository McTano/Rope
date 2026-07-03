 module

public import RowPredicates.Label

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

inductive PreRow.disjoint : PreRow -> PreRow -> Prop where
  | refl : disjoint .empty .empty
  | extend : disjoint r1 r2 -> l1 ≠ l2 -> r1.lack l2 -> r2.lack l1 -> disjoint (.extend r1' l1 t1) (.extend r2' l2 t2)

inductive PreRow.unique_labels : PreRow -> Prop where
  | empty : unique_labels .empty
  | rVar : unique_labels (.rVar s)
  | extend : unique_labels r -> lack r l -> unique_labels (extend r l t)

-- Row is concrete (Has explicit labels and is not a variable)
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

-- I'll have to see how it feels to induct over these types?
inductive Row : Type where
| mk (inner : PreRow)
     (wf : Row.WF inner) : Row
-- Row must be implemented on top of PreRow and bundle well-formedness invariant

inductive Ty : Type where
| mk (inner : PreTy)
     (wf : Ty.WF inner) : Ty

notation "{}" => Row.empty
notation l " : " t ", " tail => Row.extend tail l t
notation "@@" t => Ty.TVar t

def Row.inner : Row -> PreRow
  | (.mk inner _) => inner

def Row.wf : (r : Row) -> Row.WF r.inner
  | (.mk _ wf) => wf



def Row.unique_labels : Row -> Prop
  | (.mk inner _) => inner.unique_labels

-- A row lacks a label iff the inner (well-formed) pre-row lacks that label
def Row.lack : Row -> Label -> Prop
  | (.mk inner _), l => inner.lack l

def Row.disjoint : Row -> Row -> Prop
  | (.mk innerL _), (.mk innerR _) => innerL.disjoint innerR

def Row.concrete : Row -> Prop
  | (.mk inner _) => inner.concrete

theorem PreRow.unique_labels_lack_extend : PreRow.unique_labels (.extend r l t) -> PreRow.lack r l := by
  intro h
  cases h
  assumption

theorem PreRow.unique_labels_extend {pr : PreRow} {l t} : PreRow.unique_labels (.extend pr l t) -> PreRow.unique_labels pr := by
  cases pr <;> intro h
  apply unique_labels.empty
  apply unique_labels.rVar
  cases h <;> assumption

theorem row_unique_labels : ∀ (r : Row), Row.concrete r -> Row.unique_labels r
  | (.mk inner wf) => by
    intro h
    cases h <;> simp [Row.unique_labels] <;> cases wf <;> constructor <;> assumption

-- This should (maybe?) bundle evidence eventually
inductive Pred : Type where
  | Leq (x: Row) (y: Row) : Pred
  | Concat (x: Row) (y: Row) (z: Row) :Pred
  | Eq (x: Row) (y: Row) : Pred

def PreRow.typeAt (r: PreRow) (l: Label) : Option PreTy :=
  match r with
    | .empty => .none
    -- 
    | .rVar _ => .none
    | .extend r' l' t =>
      if (l = l')
      then .some t
      else typeAt r' l

-- This should propagate the well-formedness invariant of the returned type
-- def typeAt (r: Row) (l: Label) : Option Ty :=
--   match r.inner.typeAt l with
--   | .some t => t

def PreRow.contained_in (r1 r2: PreRow) : Prop :=
  forall (l1 : Label), (typeAt r1 l1) = (typeAt r2 l1)

def Row.contained_in (a b : Row) : Prop :=
  a.inner.contained_in b.inner
  
instance : LE Row where
  le := Row.contained_in

def Row.contained_in_trans {r1 r2 r3 : Row} (h_1_2: contained_in r1 r2) (h_2_3: contained_in r2 r3): contained_in r1 r3 := by
  intro l;
  rw [h_1_2, h_2_3]

instance : Std.IsPreorder Row where
  le_refl := λ x =>
    by intro l
       rfl
  le_trans := λ _ _ _ => Row.contained_in_trans