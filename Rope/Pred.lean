module

public import Rope.Kind
public import Rope.Label
public import Rope.Term
public import Rope.Basic

@[expose] public section

namespace Pred

-- This should (maybe?) bundle evidence eventually
inductive Pred : Type where
  | Leq (x: Row) (y: Row) : Pred
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Concat (x: Row) (y: Row) (z: Row) : Pred
  | Eq (x: Row) (y: Row) : Pred

inductive Entailment : Pred -> Pred -> Prop where
  -- | .refl () () : Pred