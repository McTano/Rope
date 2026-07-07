module

public import Rope.Kind
public import Rope.Label

namespace Term

@[expose] public section

open Label Kind

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

-- Assert that all fields in the field list have a term which satisfies the given propositional predicate
inductive AllFields : (Pred: Term -> Prop) -> List Term -> Prop where
  | Nil : (AllFields Pred [])
  | Cons : Pred t -> AllFields Pred fields -> (AllFields Pred ((Term.Field l t)::fields))

-- Well-Kindedness Judgement
inductive Term.WK : Term -> Kind -> Prop where
  | RVar : (name : String) -> WK (.RVar name) KRow
  | TVar : (name : String) -> WK (.TVar name) KTy
  | TFun : (Term.WK arg Ty) -> (Term.WK ret Ty) -> (Term.WK (TFun arg ret) Ty)
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
