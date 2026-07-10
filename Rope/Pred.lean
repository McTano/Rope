module

public import Rope.Kind
public import Rope.Label
public import Rope.Term
public import Rope.Basic

@[expose] public section

namespace Pred

-- Q:? How much work can we do on entailment abstracting the structure of rows?

-- TODO This should almost certainly be mutually inductive with Row and Pred
-- This should (maybe?) bundle evidence eventually
inductive Pred : Type where
  | Contain (x: Row) (y: Row) : Pred
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Combine (x: Row) (y: Row) (z: Row) : Pred
  -- Eq can defined in terms of Combine, at the cost of always introducing another type variable
  -- | Eq (x: Row) (y: Row) : Pred
  -- May want separate disjointness or lack constraints.
  | TyEq (t1 t2 : Ty) : Pred

inductive Entail : Pred -> Pred -> Prop where
  -- | Contain : (x ≤ y) -> Entail x y