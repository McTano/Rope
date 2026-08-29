module

public import Rope.Label

@[expose] public section

namespace Pre

open Label

-- TODO add Preds 
-- After removing the rVar case, this now represents a ground row (but it can still contain type and label variables)
mutual
inductive Row : Type where
  | empty : Row -- (Identity for Concat)
  | extend (r : Row) (l : Label)  (t : Ty) : Row

inductive Ty : Type where
  | TVar (name : String) : Ty
  | TFun (arg: Ty) (ret: Ty) : Ty
  | Singleton : Label -> Ty
  | Pi : Row -> Ty
  | Sigma : Row -> Ty
  | Qual : Pred -> Ty -> Ty

inductive Pred : Type where
  | Contain (x: Row) (y: Row) : Pred
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Combine (x: Row) (y: Row) (z: Row) : Pred
  -- Eq can defined in terms of Combine, at the cost of always introducing another type variable
  -- | Eq (x: Row) (y: Row) : Pred
  -- May want separate disjointness or lack constraints.
  | TyEq (t1 t2 : Ty) : Pred
end

def Pi := Ty.Pi
def Sigma := Ty.Sigma

notation "{}" => Row.empty
notation l " : " t " , " r => Row.extend r l t
notation "@@" t => Ty.TVar t


notation "''" l => Label.explicit l
-- #check ("label" : @@"t", {})
-- #check {} = ("hello" : (Pi {}) , {})

deriving instance Repr for Row

def Row.type_at (r: Row) (l: Label) : Option Ty :=
  match r with
    | .empty => .none
    | .extend r' l' t =>
        if l = l'
        then .some t
        else type_at r' l

inductive Row.lack : Row -> (Label) -> Prop where
  | empty : Row.lack .empty l
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
  | extend : unique_labels r -> lack r l -> unique_labels (extend r l t)

theorem Row.unique_labels_lack_extend : Row.unique_labels (.extend r l t) -> Row.lack r l := by
  intro h
  cases h
  assumption

theorem Row.unique_labels_extend {pr : Row} {l t} : Row.unique_labels (.extend pr l t) -> Row.unique_labels pr := by
  cases pr <;> intro h
  apply unique_labels.empty
  cases h
  assumption

-- Row is concrete (Has explicit labels and is not a variable)
-- `concrete` is shallow, so it imposes no constraints on structures nested inside the row
inductive Row.concrete : Row -> Prop where
  | empty : concrete .empty
  | extend : concrete r -> Label.concrete l -> lack r l -> concrete (extend r l t)

inductive Row.ground : Row -> Prop where
  | empty : ground .empty
  | extend {r l t} : ground (extend r l t)
  
theorem conc_inner : Row.concrete (a.extend l t) -> Row.concrete a :=
  by intro h; cases h; trivial

-- theorem ground_inner : Row.ground (a.extend l t) -> Row.ground a :=
--   by intro h; cases h; trivial


theorem lacks_extend_lacks {r: Row} {l1 l2: Label} {t: Ty} (h_lack: Row.lack (r.extend l2 t) l1) : Row.lack r l1 :=
  match h_lack with
  | .extend h' _ => h'


-- TODO Add Preds
-- Well-formed rows are equivalent iff they are equal up to reordering of fields.
-- Equivalence under a context/substitution will be defined later.
mutual
inductive In : Label -> Ty -> Row -> Prop where
  | first (l: Label) (t: Ty) (a: Row) (t' : Ty) : Ty.Equiv t t' -> In l t (.extend a l t')
  | tail (l l' : Label) (t t': Ty) (a : Row)  : In l t a -> In l t (.extend a l' t')
  -- | equiv (l : Label) (t t' : Ty) (te : Ty.Equiv t t') (a : Row ): In l t a -> In l t' a

inductive le : Row -> Row -> Prop where
  | empty {r : Row} : le .empty r
  | extendR {a b : Row} {l : Label} {t : Ty} : (a_le_b: le a b) -> le a (b.extend l t)
  | extendL (a b: Row) (l : Label) (t : Ty) : (a_le_b: le a b) -> (h_in : In l t b) -> le (l : t, a) b

-- Types are equivalent iff they are equal up to equivalence of in all subtree
inductive Ty.Equiv : Ty  -> Ty  -> Prop where
  | TVar : Ty.Equiv (Ty.TVar s) (Ty.TVar s)
  | Singleton : Ty.Equiv (Ty.Singleton l) (Ty.Singleton l)
  | Pi {a b : Row} : le a b -> le b a -> Ty.Equiv (.Pi a) (.Pi b)
  | Sigma {a b : Row} : le a b -> le b a -> Ty.Equiv (.Sigma a) (.Sigma b)
  | TFun : Ty.Equiv a1 a2 -> Ty.Equiv r1 r2 -> Ty.Equiv (.TFun a1 r1) (.TFun a2 r2)
  | Qual : Pred.Equiv p1 p2 -> Ty.Equiv t1 t2 -> Ty.Equiv (.Qual p1 t1) (.Qual p2 t2)

inductive Pred.Equiv : Pred -> Pred -> Prop where
  | Contain {x1 x2 y1 y2 : Row} : le x1 x2 -> le x2 x1 -> le y1 y2 -> le y2 y1 -> Pred.Equiv (.Contain x1 y1) (.Contain x2 y2)
    -- Garrett-style 3-place concatenation predicate
    -- x + y ~ z
  | Combine {x1 x2 y1 y2 z1 z2: Row} :
    le x1 x2 -> le x2 x1 ->
    le y1 y2 -> le y2 y1 ->
    le z1 z2 -> le z2 z1 ->
    Pred.Equiv (.Combine x1 y1 z1) (.Combine x2 y2 z2)
  | TyEq {a1 a2 b1 b2 : Ty} : (Ty.Equiv a1 a2) -> (Ty.Equiv b1 b2) ->  Pred.Equiv (.TyEq a1 b1) (.TyEq a2 b2)
end




-- Probably simpler version of le
-- If we allow rVar as a case of Row, then by this definition, rVar is ≤ any row
def le' (a b : Row) := (∀ {l : Label} {t : Ty}, In l t a -> In l t b)

-- def le' (a b : Row) := (∀ {l : Label} {t : Ty}, In l t a.inner -> In l t b.inner)

@[refl]
theorem le'.refl {a : Row} : le' a a := id
theorem le'.trans {a b c : Row} : le' a b -> le' b c -> le' a c :=
  λ h1 h2 l t h =>
    by
      apply h2
      apply h1
      apply h

instance : LE Row where
  le := le


-- Rows are equivalent iff they are LE each other
def Row.Equiv (a b : Row) : Prop := a ≤ b ∧ b ≤ a

theorem le.empty_is_refl {r : Row} : r ≤ .empty <-> r = .empty :=
  Iff.intro (
    λ h =>
      match h with
      | le.empty => rfl
  ) (
    λ h => by
      rw [h];
      apply le.empty)

mutual
@[refl]
theorem le.refl {x : Row} : le x x :=
  match x with
  | .empty => .empty
  | Row.extend r l t => by
    apply le.extendL <;> try trivial
    apply le.extendR <;> try trivial
    apply le.refl <;> trivial
    apply In.first <;> try trivial
    apply Ty.Equiv.refl

@[refl]
theorem Ty.Equiv.refl {t : Ty} : Ty.Equiv t t :=
match t with
| .TVar _ => .TVar
| .Singleton _ => .Singleton
| .TFun arg ret =>
  @Ty.Equiv.TFun arg arg ret ret .refl .refl
| .Pi _ =>
  @Ty.Equiv.Pi _ _ .refl .refl
| .Sigma _ =>
  @Ty.Equiv.Sigma _ _ .refl .refl
| .Qual _ _ => Ty.Equiv.Qual .refl .refl

@[refl]
theorem Pred.Equiv.refl {x : Pred} : Pred.Equiv x x :=
  match x with
  | .Contain _ _ => Pred.Equiv.Contain .refl .refl .refl .refl
  | .Combine _ _ _ =>
    Pred.Equiv.Combine .refl .refl .refl .refl .refl .refl
  | .TyEq _ _ => Pred.Equiv.TyEq .refl .refl
end

@[refl]
theorem Row.Equiv.refl {r: Row} : Row.Equiv r r :=
  .intro .refl .refl

@[symm]
theorem Row.Equiv.symm : ∀ {x y : Row}, Row.Equiv x y → Row.Equiv y x :=
  λ h =>
    match h with
    | (And.intro l r) => (And.intro r l)

mutual
@[symm]
theorem Ty.Equiv.symm : ∀ {x y : Ty}, Ty.Equiv x y → Ty.Equiv y x :=
  λ h =>
    match h with
    | .TVar => Ty.Equiv.TVar
    | .Singleton => .Singleton
    | .TFun h1 h2 => .TFun (Ty.Equiv.symm h1) (Ty.Equiv.symm h2)
    | @Ty.Equiv.Pi _ _ hl hr => @.Pi _ _ hr hl
    | @Ty.Equiv.Sigma  _ _ hl hr   => @.Sigma _ _ hr hl
    | .Qual h1 h2 => .Qual (Pred.Equiv.symm h1) (Ty.Equiv.symm h2)

@[symm]
theorem Pred.Equiv.symm : ∀ {p q : Pred}, Pred.Equiv p q → Pred.Equiv q p :=
  λ h =>
    match h with
    | .Contain a b c d => .Contain b a d c
    | .Combine a b c d e f => .Combine b a d c f e
    | .TyEq a b => .TyEq a.symm b.symm
end

theorem le.extendL_cancel {a b : Row} (h_le : (l : t, a) ≤ b) : a ≤ b :=
  match h_le with
  | .extendL _ _ _ _ h _ => h
  | .extendR _ => 
    by
    apply le.extendR
    apply le.extendL_cancel
    trivial


mutual
theorem in_equiv_in {l t1 t2} (a: Row) (h_in : In l t1 a) (e : Ty.Equiv t1 t2) : In l t2 a :=
  match h_in with
  | .first _ _ a' tx e' =>
    In.first l t2 a' tx (
    match t1, t2, tx, e, e' with
    | .Pi a, .Pi b, .Pi c, .Pi a_le_b b_le_a, .Pi a_le_c c_le_a =>
      Ty.Equiv.Pi (le.trans b_le_a  a_le_c) (le.trans c_le_a a_le_b)
    | .Sigma _, .Sigma _, .Sigma _, .Sigma a_le_b b_le_a, .Sigma a_le_c c_le_a =>
      Ty.Equiv.Sigma (le.trans b_le_a  a_le_c) (le.trans c_le_a a_le_b)
    | .Qual p1 t1, .Qual p2 t2, .Qual p3 t3, .Qual pe te, .Qual pe' te' =>
      Ty.Equiv.Qual (Pred.Equiv.trans pe.symm pe') (Ty.Equiv.trans te.symm te')
    | .TFun _ _, .TFun _ _, .TFun _ _, .TFun ae re, .TFun ae' re' =>
      Ty.Equiv.TFun (Ty.Equiv.trans ae.symm ae')  (Ty.Equiv.trans re.symm re')
    | .Singleton _, .Singleton _, .Singleton _, .Singleton, .Singleton =>
      .Singleton
    | .TVar _, .TVar _, .TVar _, .TVar, .TVar => .TVar)
  | .tail _ _ _ _ _ h_in' =>
    by
    apply In.tail
    apply in_equiv_in _ h_in' e
termination_by (sizeOf t1 + sizeOf t2 + sizeOf a)

theorem in_le_in {l a b t} (h_in : In l t a) (hle : a ≤ b)   : In l t b :=
  match h_in with
  | .first _ _ a' t' e =>
    have h_le_r : (l : t' , a') ≤ b := hle
    match hle with
    | @le.extendR _ b' _ _ hle' => by
      apply In.tail
      apply in_le_in _ hle'
      apply In.first _ _ _ _ e
    | .extendL _ _ _ _ a'_le_b l_t'_in_b =>
      in_equiv_in _ l_t'_in_b e.symm
  | .tail _ _ _ _ a' hin' => by
    have lem : a' ≤ b := by
      apply le.extendL_cancel hle
    apply in_le_in hin' lem
termination_by (sizeOf a + sizeOf b + sizeOf t)

theorem le.trans {a b c : Row}
  (h_a_b : a ≤ b) (h_b_c : b ≤ c) : a ≤ c :=
  match a, b with
  | {}, {} => .empty
  | {}, (lb : tb, b) => .empty
  | (la : ta, a'), {} => (by contradiction)
  | (la : ta, a'), (lb : tb, b') =>
    match h_a_b with
    | .extendL _ _ _ _ a'_le_b hin' =>
      have hbc' : (lb : tb , b') ≤ c := h_b_c
      match h_b_c with
      | @le.extendR  _ c' lc tc hle' =>
        have lem'' : (la : ta, a') ≤ c' :=
          le.trans h_a_b hle'
        have lem : a' ≤ c' :=
          le.trans a'_le_b hle'
        have lem' : a' ≤ (lc : tc, c') :=
          .extendR lem
        by
        apply le.extendR lem''
      | .extendL _ _ _ _ b'_le_c hin'' =>
        by
        apply le.extendL _ _ _ _
          (le.trans a'_le_b hbc')
          (in_le_in hin' hbc')
    | .extendR a_le_b' =>
      by
      apply le.trans a_le_b' _
      apply le.extendL_cancel h_b_c
termination_by (sizeOf a + sizeOf b + sizeOf c)

theorem Ty.Equiv.trans {x y z : Ty} :
  Ty.Equiv x y → Ty.Equiv y z → Ty.Equiv x z :=
  λ h1 h2 =>
    match x, y, z with
    | .TVar x', .TVar y', .TVar z' =>
      by cases h1 ; cases h2; apply Ty.Equiv.refl
    | .Singleton x', .Singleton y', .Singleton z' =>
      by cases h1 ; cases h2; apply Ty.Equiv.refl
    | .TFun _ _, _, _ =>
        match h1, h2 with
        | @Ty.Equiv.TFun _ _ _ _ h1a h1r, Ty.Equiv.TFun h2a h2r =>
          Ty.Equiv.TFun (Ty.Equiv.trans h1a h2a) (Ty.Equiv.trans h1r h2r)
    | .Pi a, .Pi b, .Pi c =>
      match h1, h2 with
      | @Ty.Equiv.Pi _ _ h_ab h_ba, Ty.Equiv.Pi h_bc h_cb => 
        have h_ac :=
          (@le.trans a b c h_ab h_bc)
        have h_ca :=
          (@le.trans c b a h_cb h_ba)
        @Ty.Equiv.Pi
        a
        c
        h_ac
        h_ca
    | .Sigma a, .Sigma b, .Sigma c =>
      match h1, h2 with
      | @Ty.Equiv.Sigma _ _ h_ab h_ba, Ty.Equiv.Sigma h_bc h_cb => 
        have h_ac :=
          (@le.trans a b c h_ab h_bc)
        have h_ca :=
          (@le.trans c b a h_cb h_ba)
        @Ty.Equiv.Sigma
        a
        c
        h_ac
        h_ca
    | .Qual p1 t1', .Qual p2 t2', .Qual p3 t3' =>
      match h1, h2 with
      | Ty.Equiv.Qual h_pxy h_txy, Ty.Equiv.Qual h_pyz h_tyz
        =>
          Ty.Equiv.Qual
            (@Pred.Equiv.trans p1 p2 p3 h_pxy h_pyz)
            (@Ty.Equiv.trans t1' t2' t3' h_txy h_tyz)
termination_by (sizeOf x + sizeOf y + sizeOf z)

theorem Pred.Equiv.trans {x y z : Pred} :
  Pred.Equiv x y → Pred.Equiv y z → Pred.Equiv x z
:=
  λ h1 h2 =>
    match y with
    | .Contain _ _ =>
      match h1, h2 with
      | @Pred.Equiv.Contain _ _ _ _ ha_xy ha_yx hb_xy hb_yx,
         Pred.Equiv.Contain ha_yz ha_zy hb_yz hb_zy =>
          .Contain
            (le.trans ha_xy ha_yz)
            (le.trans ha_zy ha_yx)
            (le.trans hb_xy hb_yz)
            (le.trans hb_zy hb_yx)
    | .Combine _ _ _ =>
      match h1, h2 with
      | @Pred.Equiv.Combine _ _ _ _ _ _ ha_xy ha_yx hb_xy hb_yx hc_xy hc_yx,
         Pred.Equiv.Combine ha_yz ha_zy hb_yz hb_zy hc_yz hc_zy =>
          .Combine
            (le.trans ha_xy ha_yz)
            (le.trans ha_zy ha_yx)
            (le.trans hb_xy hb_yz)
            (le.trans hb_zy hb_yx)
            (le.trans hc_xy hc_yz)
            (le.trans hc_zy hc_yx)
    | .TyEq _ _ =>
      match h1, h2 with
      | @Pred.Equiv.TyEq _ _ _ _ ha_xy hb_xy,
         Pred.Equiv.TyEq ha_yz hb_yz =>
          .TyEq
            (Ty.Equiv.trans ha_xy ha_yz)
            (Ty.Equiv.trans hb_xy hb_yz)
termination_by (sizeOf x + sizeOf y + sizeOf z)
end


theorem in_extend : In l t a -> In l t (l' : t', a) := by
  intro h_in
  apply In.tail _ _ _ _ _ h_in


theorem Row.Equiv.trans {x y z: Row} (h_x_y : Row.Equiv x y) (h_y_z : Row.Equiv y z) : Row.Equiv x z :=
  And.intro (le.trans h_x_y.left h_y_z.left) (le.trans h_y_z.right h_x_y.right)

instance : Std.IsPreorder Row := ⟨λ _ => le.refl, λ _ _ _ => le.trans⟩


-- This definition of equivalence is syntactic, up to reordering of fields
-- Equivalence of rows with respect to a context or substitution will be defined over quotients of well-formed rows and types
instance Ty.instSetoid : Setoid Ty where
  r := Ty.Equiv
  iseqv := ⟨λ _ => .refl, .symm, .trans⟩

instance Row.instSetoid : Setoid Row where
  r := Row.Equiv
  iseqv := ⟨λ _ => .refl, .symm, .trans⟩

instance Pred.instSetoid : Setoid Pred where
  r := Pred.Equiv
  iseqv := ⟨λ _ => .refl, .symm, .trans⟩


theorem le_equiv (a b : Row) : (le a b ↔ le' a b) :=
  .intro
  (λ h l t h' =>
    match h with
    | le.empty => by cases h'
    | @le.extendR _ b' l' t' a_le_b => by
      rw [le_equiv] at a_le_b <;> try trivial
      have lem : In l t b' := by
        apply a_le_b h'
      apply In.tail l l' t t' b' lem
    | .extendL a' _ l' t' h_le h_in => by
      cases h'
      case first te =>
        apply in_equiv_in _ h_in te.symm
      case tail h_in' =>
        rw [le_equiv] at h_le <;> try trivial
        apply h_le h_in'
  )
  (
    λ h =>
      match a with
      | .empty => .empty
      | .extend a' la ta =>
        match b with
        | .empty => by
          have lem : In la ta {} :=
            by
            apply h
            apply In.first
            apply Ty.Equiv.refl
          cases lem
        | .extend b' lb tb => by
          have lem : In la ta (lb : tb , b') := by
            apply h
            apply In.first
            rfl
          have lem' : le' a' (lb : tb, b') := by
            intro lx tx hx
            apply h
            apply in_extend hx
          rw [<-le_equiv] at lem'
          apply le.extendL <;> try trivial
  )
