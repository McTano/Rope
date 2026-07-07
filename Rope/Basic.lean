module

public import Rope.WF

@[expose] public section

def Row : Type := Quotient WF.Row.instSetoid

def Ty : Type := Quotient WF.Ty.instSetoid

end