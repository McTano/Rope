module

public import RowPredicates.Kind
public import RowPredicates.Label
public import RowPredicates.Term
public import RowPredicates.WF

@[expose] public section

namespace Pred

open Label Kind Term WF Pred

-- This should (maybe?) bundle evidence eventually
inductive Pred : Type where
  | Leq (x: WF.Row) (y: WF.Row) : Pred
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Concat (x: WF.Row) (y: WF.Row) (z: WF.Row) :Pred
  | Eq (x: WF.Row) (y: WF.Row) : Pred

inductive PredTerm : Type where
  | Leq : Term -> Term -> PredTerm
  | Eq : Term -> Term -> PredTerm
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Concat : Term -> Term -> Term -> PredTerm

-- inductive PredTerm.WK : PredTerm -> Prop where
--   | Leq : Term.WK x KRow -> Term.WK y KRow -> PredTerm.WK (PredTerm.Leq x y)
--   | Eq : Term.WK x KRow -> Term.WK y KRow -> Term.WK y KRow -> PredTerm.WK (PredTerm.Concat x y z)
--   | Concat : Term.WK x KRow -> Term.WK y KRow -> Term.WK y KRow -> PredTerm.WK (PredTerm.Concat x y z)
