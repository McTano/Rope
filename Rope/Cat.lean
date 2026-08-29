module
-- public import Rope.Pre
-- public import Rope.WF
public import Rope.Label

namespace Cat
open Label

-- This file explores encoding Rows using singleton rows and concatenation.

@[expose] public section

mutual
inductive Ty where
| TVar (s : String) : Ty
| Pi (r : Row) : Ty
| TFun (t1 t2 : Ty) : Ty

inductive Row where
| Empty : Row
| Labeled (l : Label) (t : Ty)
| Cat (a : Row) (b : Row) : Row
end

notation "[]" => Row.Empty
notation "[ " l " : " t " ]" => Row.Labeled l t
infixl:110 " + " => Row.Cat

notation "@@" t => Ty.TVar t


mutual
inductive Disjoint : Row -> Row -> Prop where
| Labeled {l l' t t'} (ne : l ≠ l') : Disjoint (.Labeled l t) (.Labeled l' t')

inductive Lacks : Row -> Label -> Prop where
| Empty : Lacks .Empty l
| Labeled {l l' t} (ne : l ≠ l') : Lacks (.Labeled l t) l'
| Cat (h_lack : Lacks a l) (ne : l ≠ l') : Lacks (a + [l' : t]) l
end


infix:90 " ⊥ " => Disjoint
notation l " ∉ " r => Lacks r l

mutual
inductive Ty.WF : Ty -> Prop where
| TVar :Ty.WF (.TVar s)
| Pi (r : Row) (wfr : Row.WF r) : Ty.WF (.Pi r)

inductive Row.WF : Row -> Prop where
| Empty : Row.WF []
| Labeled {l t} (wft : Ty.WF t) : Row.WF (.Labeled l t)
| Cat (a b : Row) (wfa : Row.WF a) (wfb : Row.WF b) (hd : Disjoint a b): Row.WF (.Cat a b)
end

-- define LE
-- prove:
-- - le is associative, commutative (symmetric), transitive
-- - Cat preserves wellformedness (given certain conditions). [Pretty much direct from the definition of Row.WF.Cat rule]


mutual
inductive Row.le : Row -> Row -> Prop where
| Empty {x} : Row.le [] x
| Labeled {t t' l} (te : Ty.equiv t t') : Row.le [l : t] [l : t']
| CatR {a b c} (hle : Row.le a b) : Row.le a (c + b)
| CatL {a b c} (hle : Row.le b c ) : Row.le (a + b) c

inductive Ty.equiv : Ty  -> Ty  -> Prop where
  | TVar : Ty.equiv (Ty.TVar s) (Ty.TVar s)
  | Pi (hle : Row.le a b) (hle' : Row.le b a) : Ty.equiv (.Pi a) (.Pi b)
  | TFun : Ty.equiv a1 a2 -> Ty.equiv r1 r2 -> Ty.equiv (.TFun a1 r1) (.TFun a2 r2)
end


instance : LE Row where
  le := Row.le

def Row.equiv (a b : Row) : Prop := a ≤ b ∧ b ≤ a

mutual
@[refl]
theorem Row.le.refl {r : Row} : r ≤ r :=
    by
    cases r
    case Empty => apply Row.le.Empty
    case Labeled =>
      apply Row.le.Labeled
      apply Ty.equiv.refl
    case Cat =>
      apply Row.le.CatL
      apply Row.le.CatR
      apply Row.le.refl

theorem Ty.equiv.refl {t : Ty} : t.equiv t :=
  by
  cases t
  case TVar s => apply Ty.equiv.TVar
  case Pi x =>
    exact Ty.equiv.Pi .refl .refl
  case TFun t1 t2 => constructor <;> apply Ty.equiv.refl
end

mutual
theorem Ty.equiv.symm {ta tb : Ty} (h : ta.equiv tb) : tb.equiv ta :=
  match h with
  | .TVar => .TVar
  | .Pi hle hle' =>  .Pi hle' hle
  | .TFun h1 h2 => .TFun h1.symm h2.symm
end

theorem Row.equiv.symm {a b : Row} (h : a.equiv b) : b.equiv a :=
  And.symm h

theorem Row.le.cancelLL (h: a + b ≤ c) : b ≤ c :=
  match h with
  | .CatL hle' => hle'
  | .CatR hle' => le.CatR (cancelLL hle')

mutual
theorem Row.le.trans {a b : Row} : a ≤ b -> b ≤ c -> a ≤ c :=
  λ hle1 hle2 =>
  match hle1 with
  | .Empty => .Empty
  | @Row.le.Labeled t t' l te => 
    match hle2 with
    | .Labeled te' => by
      apply Row.le.Labeled _
      apply Ty.equiv.trans te te'
    | @Row.le.CatR _ b' _ hle2'   =>
      by
      apply Row.le.CatR
      have lem : [l : t] ≤ [l : t'] :=
        Row.le.Labeled te
      apply Row.le.trans lem hle2'
  | @Row.le.CatL _ b' _ hle' =>
    by
    apply Row.le.CatL
    apply Row.le.trans hle' hle2
  | @Row.le.CatR _ b' c' hle' => by
    have lem : b' ≤ c := Row.le.cancelLL hle2
    apply Row.le.trans hle' lem

theorem Ty.equiv.trans {ta tb tc : Ty} : ta.equiv tb -> tb.equiv tc -> ta.equiv tc :=
  λ h1 h2 =>
  match h1, h2 with
  | .TVar, .TVar => .TVar
  | .Pi h1 h1', .Pi h2 h2' =>
    Ty.equiv.Pi (Row.le.trans h1 h2) (Row.le.trans h2' h1')
  | .TFun h1 h2, .TFun h1' h2' =>
    by
    apply Ty.equiv.TFun
    apply Ty.equiv.trans h1 h1'
    apply Ty.equiv.trans h2 h2'
end