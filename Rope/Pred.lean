module

public import Rope.Kind
public import Rope.Label
public import Rope.Term
public import Rope.Basic

@[expose] public section

namespace Pred


-- This should (maybe?) bundle evidence eventually
inductive Pred : Type where
  | Contain (x: Row) (y: Row) : Pred
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Combine (x: Row) (y: Row) (z: Row) : Pred
  | Eq (x: Row) (y: Row) : Pred

inductive Entail : Pred -> Pred -> Prop where
  -- | Contain : (x ≤ y) -> Entail x y