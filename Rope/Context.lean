module

public import Rope.Kind
public import Rope.Label
public import Rope.WF
public import Std.Data.HashMap


namespace Context

open Kind Label


def KindType (k : Kind) : Type :=
  match k with
  | .KRow => WF.Row
  | .KTy => WF.Ty
  | .KLabel => Label

def KindContext : Kind -> Type := λ k => Std.HashMap String (KindType k)

def KindContext.empty {k : Kind} : KindContext k := .emptyWithCapacity

structure Context where
  rowContext : KindContext .KRow := .empty
  typeContext : KindContext .KTy := .empty
  labelContext : KindContext .KLabel := .empty
  getContext (k: Kind) : KindContext k :=
      match k with
      | .KRow => rowContext
      | .KTy => typeContext
      | .KLabel => labelContext
  get {k : Kind} (s: String) : Option (KindType k) := (getContext k).get? s
  insert {k : Kind} (s: String) : Option (KindType k) := (getContext k).get? s

def Context.empty : Context := {}

inductive WithContext {c : Context} (T : Type): Type where
| wrap : T -> WithContext T

def unwrap : WithContext (c := c) T -> T
| .wrap x => x

def RowWithContext {c : Context} := WithContext (c := c) WF.Row
def TyWithContext {c : Context} := WithContext (c := c) WF.Ty
def LabelWithContext {c : Context} := WithContext (c := c) Label
