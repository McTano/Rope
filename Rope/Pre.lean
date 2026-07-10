module

public import Rope.Label

@[expose] public section

namespace Pre

open Label

-- TODO add Preds 
mutual
inductive Row : Type where
  | empty : Row -- (Identity for Concat)
  | rVar : String -> Row
  | extend (r : Row) (l : Label)  (t : Ty) : Row

inductive Ty : Type where
  | TVar (name : String) : Ty
  | TFun (arg: Ty) (ret: Ty) : Ty
  | Singleton : Label -> Ty
  | Pi : Row -> Ty
  | Sigma : Row -> Ty
  -- | Qual : Pred -> Ty -> Ty
end

def Row.type_at (r: Row) (l: Label) : Option Ty :=
  match r with
    | .empty => .none
    | .rVar _ => .none
    | .extend r' l' t =>
        if l = l'
        then .some t
        else type_at r' l

inductive Row.lack : Row -> (Label) -> Prop where
  | empty : Row.lack .empty l
  | rVar : l ≠ l -> Row.lack (Row.rVar s) l
  | extend : Row.lack r l -> l ≠ l' -> Row.lack (extend r l' t) l

theorem Row.lack_extend_lack : lack (.extend r l' t) l -> lack r l
| .extend h _ => h

inductive Row.has_label : Row -> Label -> Prop where
  | first {r l t} : has_label (.extend r l t) l
  | extend {r l l' t} : (has_label r l) -> has_label (.extend r l' t) l

theorem Row.has_label_neg_lack (h: has_label r l): ¬lack r l :=
  λ hn =>
    match h with
    | .first => match hn with
      | .extend _ _ => by contradiction
    | .extend h' =>  (has_label_neg_lack h' (lack_extend_lack hn))

inductive Row.disjoint : Row -> Row -> Prop where
  | refl : disjoint .empty .empty
  | extend : disjoint r1 r2 -> l1 ≠ l2 -> r1.lack l2 -> r2.lack l1 -> disjoint (.extend r1' l1 t1) (.extend r2' l2 t2)



theorem Row.disjoint_symm {r1 r2 : Row} (h: Row.disjoint r1 r2) : Row.disjoint r2 r1 :=
  match h with
  | .refl => .refl
  | .extend a b c d => by
    apply Row.disjoint.extend
    constructor
    symm
    exact b
    exact .empty
    exact .empty

inductive Row.unique_labels : Row -> Prop where
  | empty : unique_labels .empty
  | rVar : unique_labels (.rVar s)
  | extend : unique_labels r -> lack r l -> unique_labels (extend r l t)

theorem Row.unique_labels_lack_extend : Row.unique_labels (.extend r l t) -> Row.lack r l := by
  intro h
  cases h
  assumption

theorem Row.unique_labels_extend {pr : Row} {l t} : Row.unique_labels (.extend pr l t) -> Row.unique_labels pr := by
  cases pr <;> intro h
  apply unique_labels.empty
  apply unique_labels.rVar
  cases h ;
  assumption

-- Row is concrete (Has explicit labels and is not a variable)
-- `concrete` is shallow, so it imposes no constraints on structures nested inside the row
inductive Row.concrete : Row -> Prop where
  | empty : concrete .empty
  | extend : concrete r -> Label.concrete l -> lack r l -> concrete (extend r l t)
