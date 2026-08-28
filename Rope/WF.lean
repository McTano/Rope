module
public import Rope.Pre
public import Rope.Label

@[expose] public section

namespace WF

open Label Pre

-- TODO add WF_Pred
-- Interdefined Well-formedness rules for Pre.Row and Pre.Ty
mutual
inductive WF_Row : (inner: Pre.Row) -> Prop where
  | empty : WF_Row .empty
  | extend : WF_Row r -> r.lack l -> (WF_Ty t) -> WF_Row (.extend r l t)

-- TODO Binders for type and row variables. I think both should be defined in Ty.
inductive WF_Ty : (inner: Pre.Ty) -> Prop where
  -- Unit type?
  -- For now, all TVars are free and double as atomic types and provide a base case for WF_Ty,
  | TVar : WF_Ty (.TVar s)
  | TFun : WF_Ty arg -> WF_Ty ret -> WF_Ty (.TFun arg ret)
  | Singleton : WF_Ty (.Singleton l)
  | Pi : WF_Row r -> WF_Ty (.Pi r)
  | Sigma : WF_Row r -> WF_Ty (.Sigma r)
  | Qual : WF_Pred p -> WF_Ty t -> WF_Ty (.Qual p t)

inductive WF_Pred : (inner :Pre.Pred) -> Prop where
  | Contain : WF_Row x -> WF_Row y -> WF_Pred (.Contain x y)
  | Combine : WF_Row x -> WF_Row y -> WF_Row z -> WF_Pred (.Combine x y z)
  | TyEq : WF_Ty t1 -> WF_Ty t2 -> WF_Pred (.TyEq t1 t2)
end

theorem WF.unique_labels {r : Pre.Row} (wf : WF_Row r) : r.unique_labels :=
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

theorem extend_equal_label (a : Pre.Row) (wfa : WF_Row a) (l : Label) (t t' : Pre.Ty) (h_lack : a.lack l) (h_in: In l t (Pre.Row.extend a l t')) :
    Ty.Equiv t t' :=
  by
    have lem : ¬ In l t a := by
      intro h_f
      apply lack_not_in h_lack h_f
    unhygienic cases h_in <;> cases wfa
    repeat trivial

theorem equal_label_equiv_type (l : Label) (t1 t2: Pre.Ty) (r : Pre.Row) (wfr : WF_Row r)
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
