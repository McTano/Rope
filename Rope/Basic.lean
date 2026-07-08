module

public import Rope.WF

@[expose] public section

-- open WF


def Row : Type := Quotient WF.Row.instSetoid

def Ty : Type := Quotient WF.Ty.instSetoid

instance : LE Row where
  le :=
    Quotient.lift₂ WF.Row.le <| by
      intro a1 b1 a2 b2 aeq beq
      cases aeq; cases beq;
      case _ ha hb =>
        
        
        sorry

-- def lack (r1 r2 : Row) : Prop :=
--   Quotient.lift WF.lack <| by
--     sorry
--     sorry
--     sorry

