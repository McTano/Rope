module

public import Rope.WF

@[expose] public section

-- open WF


def Row : Type := Quotient WF.Row.instSetoid

def Ty : Type := Quotient WF.Ty.instSetoid

def Pred : Type := Quotient WF.Pred.instSetoid

-- instance : LE Row where
--   le :=
--     Quotient.lift₂ WF.Row.le <| by
--       intro a1 b1 a2 b2 aeq beq
--       cases aeq; cases beq;
--       case _ ha1 ha2 hb1 hb2 =>
--         sorry

-- def lack (r1 r2 : Row) : Prop :=
--   Quotient.lift WF.lack <| by
--     sorry
--     sorry
--     sorry

