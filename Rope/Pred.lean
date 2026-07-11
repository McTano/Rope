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

inductive Entail : Pred -> Pred -> Prop where
  -- | Contain : (x ≤ y) -> Entail x y