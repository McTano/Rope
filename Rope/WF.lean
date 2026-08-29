module
public import Rope.Pre
public import Rope.Label

@[expose] public section

namespace WF

open Label Pre

-- Interdefined Well-formedness rules for Pre.Row and Pre.Ty
mutual
inductive Row.WF : (inner: Pre.Row) -> Prop where
  | empty : Row.WF .empty
  | extend : Row.WF r -> r.lack l -> (Ty.WF t) -> Row.WF (.extend r l t)

-- TODO Binders for type and row variables. I think both should be defined in Ty.
inductive Ty.WF : (inner: Pre.Ty) -> Prop where
  -- Unit type?
  -- For now, all TVars are free and double as atomic types and provide a base case for Ty.WF,
  | TVar : Ty.WF (.TVar s)
  | TFun : Ty.WF arg -> Ty.WF ret -> Ty.WF (.TFun arg ret)
  | Singleton : Ty.WF (.Singleton l)
  | Pi : Row.WF r -> Ty.WF (.Pi r)
  | Sigma : Row.WF r -> Ty.WF (.Sigma r)
  | Qual : Pred.WF p -> Ty.WF t -> Ty.WF (.Qual p t)

inductive Pred.WF : (inner :Pre.Pred) -> Prop where
  | Contain : Row.WF x -> Row.WF y -> Pred.WF (.Contain x y)
  | Combine : Row.WF x -> Row.WF y -> Row.WF z -> Pred.WF (.Combine x y z)
  | TyEq : Ty.WF t1 -> Ty.WF t2 -> Pred.WF (.TyEq t1 t2)
end


theorem WF.unique_labels {r : Pre.Row} (wf : Row.WF r) : r.unique_labels :=
  match wf with
  | .empty => .empty
  | .extend r_wf r_lack_l ty_wf => Pre.Row.unique_labels.extend (WF.unique_labels r_wf) r_lack_l

theorem in_not_lack : In l t a -> a.lack l -> False :=
  λ h h' =>
  match h with
  | .first _ _ _ _ _ => by
    cases h'
    contradiction
  | .tail _ _ _ _ r' h_in => by
    cases h'
    apply in_not_lack <;> assumption

theorem lack_not_in : a.lack l -> In l t a -> False := by
  intro h h'
  cases a <;>
  cases h <;> cases h'
  trivial
  apply lack_not_in <;> trivial

theorem lack_contra (a : Pre.Row) (l : Label) (t : Pre.Ty) : ¬ (Pre.Row.extend a l t).lack l :=
  λ h =>
    by
      cases h;
      contradiction

theorem extend_unequal_label (a : Pre.Row) (l l' : Label) (t t' : Pre.Ty) (h_neq : l ≠ l') (h_in: In l t (.extend a l' t')): In l t a :=
  match h_in with
  | .first _ _ _ _ _ => by contradiction
  | .tail _ _ _ _ _ _ => by assumption

theorem lack_inner_implies_equal (a : Pre.Row) (l l' : Label) (t t': Pre.Ty) : In l t (a.extend l' t') -> a.lack l -> l = l' := by
  intro h h'
  cases h
  trivial
  cases (@lack_not_in l t a h' (by trivial))

theorem extend_equal_label (a : Pre.Row) (wfa : Row.WF a) (l : Label) (t t' : Pre.Ty) (h_lack : a.lack l) (h_in: In l t (Pre.Row.extend a l t')) :
    Ty.Equiv t t' :=
  by
    have lem : ¬ In l t a := by
      intro h_f
      apply lack_not_in h_lack h_f
    unhygienic cases h_in <;> cases wfa
    repeat trivial

theorem equal_label_equiv_type (l : Label) (t1 t2: Pre.Ty) (r : Pre.Row) (wfr : Row.WF r)
  (h1 : In l t1 r) (h2 : In l t2 r) : Ty.Equiv t1 t2 :=
      match h1, h2 with
      | .first _ _ _ _ e, .first _ _ _ _ e' =>
        Ty.Equiv.trans e e'.symm
      | .first _ _ _ _ e, .tail _ _ _ _ _ i =>
        by
          cases wfr
          case extend lack _ =>
          cases (in_not_lack i lack)
      | .tail _ _ _ _ _ i, .first _ _ _ _ e =>
        by
          cases wfr
          case extend lack _ =>
          cases (in_not_lack i lack)
      | .tail _ _ _ _ _ i, .tail _ _ _ _ _ i' =>
        by
          cases wfr
          apply equal_label_equiv_type <;> trivial
