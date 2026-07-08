module
public import Rope.Pre
public import Rope.Label

@[expose] public section

namespace WF

open Label

-- Interdefined Well-formedness rules for Pre.Row and Pre.Ty
mutual
inductive WF_Row : (inner: Pre.Row) -> Prop where
  | empty : WF_Row .empty
  | rVar : WF_Row (.rVar s)
  | extend : WF_Row r -> r.lack l -> (WF_Ty t) -> WF_Row (.extend r l t)

inductive WF_Ty : (inner: Pre.Ty) -> Prop where
  | TVar : WF_Ty (.TVar s)
  | TFun : WF_Ty arg -> WF_Ty ret -> WF_Ty (.TFun (arg: Pre.Ty) (ret: Pre.Ty))
  | Singleton : WF_Ty (.Singleton l)
  | Pi : WF_Row r -> WF_Ty (.Pi r)
  | Sigma : WF_Row r -> WF_Ty (.Sigma r)
end

theorem WF.unique_labels {r : Pre.Row} (wf : WF_Row r) : r.unique_labels :=
  match wf with
  | .empty => .empty
  | .rVar => .rVar
  | .extend r_wf r_lack_l ty_wf => Pre.Row.unique_labels.extend (WF.unique_labels r_wf) r_lack_l

-- TODO set up wellfounded induction over Rows and Tys
structure Row : Type where
  inner : Pre.Row
  wf : WF_Row inner
-- Row must be implemented on top of Pre.Row and bundle well-formedness invariant

structure Ty : Type where
  inner : Pre.Ty
  wf : WF_Ty inner


def Row.unique_labels : Row -> Prop
  | .mk inner _ => inner.unique_labels

-- A row lacks a label iff the inner (well-formed) pre-row lacks that label
def Row.lack : Row -> Label -> Prop
  | ⟨inner, _⟩, l => inner.lack l

def Row.disjoint : Row -> Row -> Prop
  | ⟨innerL, _⟩, ⟨innerR, _⟩ => innerL.disjoint innerR

def Row.concrete : Row -> Prop
  | ⟨inner, _⟩ => inner.concrete

@[match_pattern]
def Row.empty : Row := ⟨.empty, .empty⟩

@[match_pattern]
def Row.extend (r: Row) (l : Label) (t : Ty) (h: r.lack l) : Row  :=
    ⟨Pre.Row.extend r.inner l t.inner, .extend r.wf h t.wf⟩

def Row.rVar (name : String) : Row :=
  ⟨.rVar name, .rVar⟩

-- @[match_pattern]
-- def Ty.TFun (t1 t2 : Ty) : Ty :=
--   ⟨Pre.Ty.TFun t1.inner t2.inner, WF_Ty.TFun t1.wf t2.wf⟩

-- @[match_pattern]
-- def Ty.Singleton (l : Label) : Ty :=
--   {
--     inner := Pre.Ty.Singleton l,
--     wf := WF_Ty.Singleton
--   }

-- @[match_pattern]
-- def Ty.Pi (r : Row) : Ty :=
--   {
--     inner := Pre.Ty.Pi r.inner,
--     wf := WF_Ty.Pi r.wf
--   }

-- @[match_pattern]
-- def Ty.Sigma (r : Row) : Ty :=
--   {
--     inner := Pre.Ty.Sigma r.inner,
--     wf := WF_Ty.Sigma r.wf
--   }

-- inductive Row.has_label : Row -> Label -> Prop where
--   | first {r l t} : (h : r.lack l) -> has_label (.extend r l t h) l
--   | extend {r l l' t} : (h : r.lack l') -> r.has_label l -> has_label (.extend r l' t h) l

def Row.has_label (r : Row) (l : Label): Prop :=
  r.inner.has_label l


def Row.type_at (r : Row) (l : Label): Option Ty :=
  match r with
  | ⟨.empty, _⟩ => .none
  | ⟨.rVar _, _⟩ => .none
  | ⟨.extend r' l' t, wf⟩ =>
     if l = l'
      then .some ⟨t, (match wf with | .extend _ _ wft => wft)⟩
      else type_at ⟨r', (match wf with | .extend wfr _ _ => wfr)⟩ l

theorem Row.type_at_is_some {r : Row} {l: Label} (h : r.has_label l) : (Option.isSome (r.type_at l) = true) :=
  match r with
  | ⟨inner, wf⟩ =>
    match inner with
    | .empty => by contradiction
    | .extend r' l' t' =>
      -- match h with
      -- | @Row.has_label.first _ _ _ _  => by
      --   simp [type_at]
      -- | @Row.has_label.extend r' l1' l2' t h_lack has_l =>
      --   dite (l1' = l2')
      --   (λ h => by
      --     simp [Row.type_at,h]
      --     )
      --   (λ h => by
      --     simp [Row.type_at, h]
      --     apply Row.type_at_is_some has_l)
        by
          by_cases (l = l')
          case _ h_pos => simp [type_at, h_pos]
          case _ h_neg =>
            cases h;
            contradiction
            simp [type_at, h_neg]
            case extend h =>
              apply Row.type_at_is_some
              simp [has_label,h]
          -- apply Row.type_at_is_some
    
def Row.type_at! (r: Row) (l: Label) (has_l : has_label r l) : Ty :=
  (r.type_at l).get (Row.type_at_is_some has_l)
  

-- def Row.le (a b : Row) : Prop :=
--   a.inner.le b.inner

theorem lacks_extend_lacks {r: Pre.Row} {l1 l2: Label} {t: Pre.Ty} (h_lack: Pre.Row.lack (r.extend l2 t) l1) : Pre.Row.lack r l1 :=
  match h_lack with
  | .extend h' _ => h'



@[match_pattern]
def Ty.TVar (s : String) : Ty :=
  ⟨Pre.Ty.TVar s, WF_Ty.TVar⟩

@[match_pattern]
def Ty.TFun (t1 t2 : Ty) : Ty :=
  ⟨Pre.Ty.TFun t1.inner t2.inner, WF_Ty.TFun t1.wf t2.wf⟩

@[match_pattern]
def Ty.Singleton (l : Label) : Ty :=
  {
    inner := Pre.Ty.Singleton l,
    wf := WF_Ty.Singleton
  }

@[match_pattern]
def Ty.Pi (r : Row) : Ty :=
  {
    inner := Pre.Ty.Pi r.inner,
    wf := WF_Ty.Pi r.wf
  }

@[match_pattern]
def Ty.Sigma (r : Row) : Ty :=
  {
    inner := Pre.Ty.Sigma r.inner,
    wf := WF_Ty.Sigma r.wf
  }

-- def get_helper : r.has_label l -> Option.isSome (type_at r l) := sorry

-- def le2_helper (e: Ty -> Ty -> Prop) (l : Label) (a b : Row) : Prop :=
--   (b.has_label l -> a.has_label l) ∧
--     (((a.has_label l ∧ b.has_label l )) -> e ((type_at a l).get) ((type_at b l).get (get_helper h.right)))

mutual
-- inductive option_equiv  : Option Ty -> Option Ty -> Prop where
--   | none : option_equiv .none .none 
--   | some : (Ty.Equiv t1 t2) -> option_equiv (.some t1) (.some t2)
inductive Row.le : Row -> Row -> Prop where
  | empty {r : Row} : Row.le .empty r
  | rVar {name : String} : Row.le (.rVar name) (.rVar name)
  | extend {a b : Row} {l : Label} {t : Ty} :
    Row.le a b -> (h_lack : a.lack l) -> b.has_label l -> Row.le (@a.extend l t h_lack) b
-- | empty : Row.le2 Row.empty Row.empty
-- | head : Row.le2
-- | mk {a b : Row} : forall l, (a.has_label l -> b.has_label l) -> () -> Row.le a b

-- Alternate definition for le. Requires 1 less assumption in the extend case, but doesn't match our induction structure as well
inductive Row.le2 : Row -> Row -> Prop where
  | refl {r : Row} : Row.le2 r r
  | extendR {a b : Row} {l : Label} {t : Ty} : (h_lack : b.lack l) -> Row.le2 a b -> Row.le2 a (b.extend l t h_lack)
  | extend2 {a b : Row} {l : Label} {ta tb : Ty} :
    Row.le2 a b -> (ha_lack : a.lack l) -> (hb_lack : b.lack l) -> Ty.Equiv ta tb -> Row.le2 (a.extend l ta ha_lack) (b.extend l tb hb_lack)
-- def Row.le (a b: Row) : Prop :=
  -- forall (l : Label), b.inner.has_label l -> a.inner.has_label l ∧ (type_at a l) = (type_at b l)

inductive Ty.Equiv : Ty  -> Ty  -> Prop where
  | TVar : Ty.Equiv (Ty.TVar s) (Ty.TVar s)
  | Singleton : Ty.Equiv (Ty.Singleton l) (Ty.Singleton l)
  | Pi : a.le b -> b.le a -> Ty.Equiv (Ty.Pi a) (Ty.Pi b)
  | Sigma : a.le b -> b.le a -> Ty.Equiv (Ty.Sigma a) (Ty.Sigma b)
  | TFun : Ty.Equiv a1 a2 -> Ty.Equiv r1 r2 -> Ty.Equiv (Ty.TFun a1 r1) (Ty.TFun a2 r2)
end

inductive Row.Equiv : WF.Row -> WF.Row  -> Prop where
  | mk {a b : WF.Row} : Row.le a b ∧ Row.le b a -> Row.Equiv a b

-- Ideas for deciding le and equiv
-- sort row and compare in order
-- convert row to a hashmap
-- Redefine a WF row to always be sorted, then define le inductively over the sorted row

instance : LE Row where
  le := Row.le

def Row.ble (a b : Row) : Bool := sorry

-- theorem Row.ble_decides_le : ∀ r1 r2: Row, r1.ble r2 = true <-> r1 ≤ r2 := by sorry

-- instance : DecidableLE Row := by
--   intro a b
--   by_cases a.ble b
--   case pos h =>
--     apply Decidable.isTrue
--     exact (Row.ble_decides_le a b).mp h
--   case neg h =>
--     sorry

theorem Row.le_inner_has_label {a b : Row} {l : Label } (h_le : a ≤ b) (h_has : a.inner.has_label l) : b.inner.has_label l :=
    match h_le with
    | .empty => by contradiction
    | @Row.le.extend a' _ l' _ a'_le_b a'_lack_l' b_has_l' =>
        dite (l = l')
        (λ hpos => by
          simp [hpos, Row.has_label,Row.extend] at *;
          exact b_has_l')
        (λ hneg =>
          match h_has with
          | .first => b_has_l'
          | .extend h => @Row.le_inner_has_label a' b _ a'_le_b h)

theorem Row.le_trans (a b c : Row) (h_a_b : a ≤ b) (h_b_c : b ≤ c) : a ≤ c :=
  match h_a_b with
  | .empty => .empty
  | .rVar => sorry
  | .extend a'_le_b h_lack h_lab =>
    .extend (le_trans _ _ _ a'_le_b h_b_c) _ (Row.le_inner_has_label h_b_c h_lab)
  -- by exact le_inner_has_label h_a_b (le_inner_has_label _ _)

  --   case right =>
  --     simp [(.≤.),Row.le] at *
  --     grind

theorem Row.le_refl : ∀ (x : Row), x ≤ x :=
  λ x =>
  match x with
  | Row.empty => .empty
  | .rVar _ => .rVar
  | ⟨Pre.Row.extend r _ _, .extend _ _ _⟩ => sorry

instance : Std.IsPreorder Row := ⟨Row.le_refl, Row.le_trans⟩

theorem Row.Equiv.refl : ∀ (r: Row), r.Equiv r :=
  λ _ => .mk (And.intro
          (instIsPreorderRow.le_refl _)
          (instIsPreorderRow.le_refl _))

theorem Row.Equiv.symm : ∀ {x y : Row}, x.Equiv y → y.Equiv x :=
  λ h =>
    match h with
    | .mk (And.intro l r) => .mk (And.intro r l)

theorem Row.Equiv.trans : ∀ {x y z: Row}, x.Equiv y → y.Equiv z → x.Equiv z := by
  intro x y z h_x_y h_y_z
  apply Equiv.mk
  apply And.intro <;>
    cases h_x_y <;> cases h_y_z <;>
    -- simp [.≤.,Row.le] at * <;>
    -- grind
    sorry

theorem Ty.Equiv.refl : ∀ x : Ty, Ty.Equiv x x :=
  λ x =>
      match x with
      | .TVar _ => .TVar
      | .Singleton _ => .Singleton
      | ⟨.TFun arg ret, WF_Ty.TFun wf_a wf_r⟩ =>
        @Equiv.TFun ⟨arg,wf_a⟩ ⟨arg,wf_a⟩ ⟨ret, wf_r⟩ ⟨ret, wf_r⟩ (.refl _) (.refl _)
      | ⟨.Pi r, WF_Ty.Pi wf_r⟩ =>
        @Equiv.Pi ⟨r, wf_r⟩ ⟨r, wf_r⟩ (Row.le_refl _) (Row.le_refl _)
      | ⟨.Sigma r, WF_Ty.Sigma wf_r⟩ =>
        @Equiv.Sigma ⟨r, wf_r⟩ ⟨r, wf_r⟩ (Row.le_refl _) (Row.le_refl _)

theorem Ty.Equiv.symm : ∀ {x y : Ty}, x.Equiv y → y.Equiv x :=
  λ h =>
    match h with
    | .TVar => Ty.Equiv.TVar
    | .Singleton => .Singleton
    | .TFun h1 h2 => .TFun (Ty.Equiv.symm h1) (Ty.Equiv.symm h2)
    | .Pi hl hr => .Pi hr hl
    | .Sigma hl hr => .Sigma hr hl

theorem Ty.Equiv.trans : ∀ {x y z : Ty}, x.Equiv y → y.Equiv z → x.Equiv z :=
  @λ x y z h1 h2 =>
    match x, y, z with
    | .TVar x', .TVar y', .TVar z' =>
      by cases h1 ; cases h2; apply Equiv.refl
    | .Singleton x', .Singleton y', .Singleton z' =>
      by cases h1 ; cases h2; apply Equiv.refl
    | ⟨.TFun _ _, _⟩, _, _ =>
        match h1, h2 with
        | @Equiv.TFun ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩ h1a h1r, Equiv.TFun h2a h2r =>
          Equiv.TFun (Ty.Equiv.trans h1a h2a) (Ty.Equiv.trans h1r h2r)
    | ⟨.Pi _, _⟩, _, _ =>
      match h1, h2 with
      | @Equiv.Pi _ ⟨_, _⟩ h_xy h_yx, Equiv.Pi h_yz h_zy => Ty.Equiv.Pi (Row.le_trans _ _ _ h_xy h_yz) (Row.le_trans _ _ _ h_zy h_yx)
    | ⟨.Sigma _, _⟩, _, _ =>
      match h1, h2 with
      | @Equiv.Sigma _ ⟨_, _⟩ h_xy h_yx, Equiv.Sigma h_yz h_zy => Ty.Equiv.Sigma (Row.le_trans _ _ _ h_xy h_yz) (Row.le_trans _ _ _ h_zy h_yx)

-- This definition of equivalence is syntactic, up to reordering of fields
-- Equivalence of rows with respect to a context or substitution will be defined over quotients of well-formed rows and types
instance Ty.instSetoid : Setoid Ty where
  r := Ty.Equiv
  iseqv := ⟨.refl, .symm, .trans⟩

instance Row.instSetoid : Setoid Row where
  r := Row.Equiv
  iseqv := ⟨.refl, .symm, .trans⟩
