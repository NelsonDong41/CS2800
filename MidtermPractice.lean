def len : list nat -> nat 
  | [] := 0 
  | (_ :: L) := nat.succ (len L)

def app : list ℕ → list ℕ → list ℕ 
  | [] L := L 
  | (x :: L1) L2 := x :: (app L1 L2)

def even : nat → bool 
    | 0 := tt 
    | 1 := ff 
    | (nat.succ (nat.succ x)) := even x

def reverse : list ℕ → list ℕ
  | [] := []
  | [x] := [x]
  | (x :: L) := app (reverse L) [x]

example : reverse [1,2,3]  = [3,2,1] := begin 
  dunfold reverse,
  dunfold app,
  refl,
end

example : reverse [1]  = [1] := begin 
  dunfold reverse,
  refl,
end

example : reverse []  = [] := begin 
  dunfold reverse,
  refl,
end

theorem len_reverse : ∀ x : list ℕ, len (reverse x) = len x :=
begin
  intro,
  cases x,
  {
    dunfold len,
    dunfold reverse,
    dunfold len,
    refl,
  },
  {
    dunfold len,
    sorry,
  }
end

theorem reverse_two_element_list: ∀ x y : ℕ, reverse (app [x] [y]) = app [y] [x]  :=
begin
   intros,
   dunfold app,
   dunfold reverse,
   dunfold app,
   refl,
end


theorem app_reverse: forall L1 L2 : list nat, 
  reverse (app L1 L2) = app (reverse L2) (reverse L1) :=
begin
  intros,
  sorry,
end

lemma p_and_false: ∀ P : Prop, P ∧ false ↔ false :=
-- ANSWER:
begin
    intros,
    split,
    {
      intros h,
      cases h,{
        assumption
      }
    },
    {
      intro,
      trivial,
    }
end


theorem or_absorb_and: ∀ P Q : Prop, P ∨ (P ∧ Q) ↔ P :=
-- ANSWER:
begin
  intros,
  split,
  {
    intro h,
    cases h,
    {
      assumption
    },
    {
      cases h,{
        assumption
      }
    }
  },
  {
    intro h,
    left,
    assumption
  }
end


theorem p_and_q_implies_p_and_q: ∀ P Q : Prop, P ∧ Q → P ∧ Q :=
begin
  intros,
  assumption
end


