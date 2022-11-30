import .ourlibrary16

section local_notation

local notation (name := local_plus) x + y := plus x y
local notation (name := local_minus) x - y := minus x y
local notation (name := local_mult) x * y := mult x y
local notation (name := local_leq) x ≤ y := leq x y = tt
local notation (name := local_ltb) x < y := ltb x y = tt
end local_notation
 
-- Q2
-- 30 Points
-- Grading comment:
-- Q2.1
-- 10 Points
-- Grading comment:
/-
prove this:
-/
-- ∀ x y : ℕ, 0 ≤ y ↔ x ≤ x + y 
lemma leq_zero_plus_right: 
  forall x y : nat, 
    (leq 0 y = tt) <-> leq x (plus x y) = tt 
:= begin
  intros,
  split,
  {
    intros h,
    revert y,
    induction x with x ih,
    {
      intros,
      dunfold plus,
      dunfold leq,
      trivial
    },
    {
      intros,
      dunfold plus,
      dunfold leq,
      have h1 := ih y h,
      assumption
    }
  },
  {
    intros,
    dunfold leq,
    trivial,
  }
end  


-- Q2.2
-- 10 Points
-- Grading comment:
-- /-
-- prove this:
-- -/
-- --   ∀ x y z : ℕ, x < y → y ≤ z → x < z 
lemma ltb_leq_ltb: 
  forall x y z : nat, 
    (ltb x y = tt) -> (leq y z = tt) -> (ltb x z = tt) := begin
  intros x y z h h1,
  revert y z,
  induction x with x ih,
  {
    intros,
    cases y,
    {
      trivial,
    },
    {
      dunfold ltb at h,
      cases z,
      {
        dunfold leq at h1,
        contradiction
      },
      {
        trivial,
      }
    }
  },
  {
    intros,
    cases y,
    {
      dunfold ltb at h,
      trivial,
    },
    {
      cases z,
      {
        dunfold ltb,
        trivial,
      },
      {
        dunfold ltb,
        dunfold ltb at h,
        dunfold leq at h1,
        have h2 := ih y z h h1,
        assumption
      }
    }
  }
end
-- Q2.3
-- 10 Points
-- Grading comment:

/- 
prove this:
-/
-- ∀ x y : ℕ, x ≤ nat.succ y → (x ≤ y ∨ x = nat.succ y)
lemma leqx0 : ∀ x : ℕ, leq x 0 = tt → x = 0
:=begin
  intro,
  cases x,
  {
    intro h,
    refl,
  },
  {
    intro h,
    rw leq at h,
    trivial,
  },
end

lemma leq_or: forall x y : nat, 
  (leq x (nat.succ y) = tt) -> or (leq x y = tt) (x = nat.succ y)
:=begin
  intro,
  induction x with x ih,
  {
    intros y h,
    left,
    refl,
  },
  {
    intros y h,
    cases y,
    {
      right,
      rw leq at h,
      have h2 := leqx0 x h,
      rw succeq,
      assumption
    },
    {
      rw leq at h,
      rw leq,
      have h1 := ih y h,
      cases h1,
      {
        left,
        assumption,
      },
      {
        right,
        rw succeq,
        assumption,
      },
    },
  },
end
-- Q3
-- 10 Points
-- Grading comment:
-- /-
-- prove the following WITHOUT USING classical.em: 
-- -/
-- -- ∀ x y : ℕ, x = y ∨ x ≠ y
-- lemma x_eq_or_ne_y: forall x y : nat, or (x = y) (not (x = y))
-- Q4
-- 10 Points
-- Grading comment:
-- /-
-- consider the function listDelete defined below:
-- -/
-- def listDelete : list nat -> nat -> list nat
--     | [] _ := []
--     | (x :: L) 0 := L 
--     | (x :: L) (nat.succ i) := x :: (listDelete L i)
-- /-
-- prove this:
-- -/
-- theorem listDelete_withinbounds:
--   forall (L : list nat) (i : nat), 
--     ltb i (len L)= tt -> 
--     nat.succ(len (listDelete L i)) = len L
-- Q5
-- 10 Points
-- Grading comment:
-- /-
-- consider the functions duplicateLast and lastElement defined below:
-- -/
def duplicateLast: list nat -> list nat 
  | [] := [] 
  | [x] := [x,x]
  | (x :: (y :: L)) := x :: (duplicateLast (y :: L))
def lastElement : list nat -> nat 
  | [] := 0 
  | [x] := x 
  | (x :: (y :: L)) := lastElement (y :: L)
-- /-
-- prove this:
-- -/
theorem duplicateLast_app_if: forall L : list nat, 
  (not (L = [])) -> (duplicateLast L = app L [(lastElement L)]) 
| [] := begin
  intros h,
  trivial,
end
| (x :: (y :: L)) := begin
  intro h,
  dunfold app,
  dunfold duplicateLast,
  rw listeq,
  split, refl,
  dunfold lastElement,
  cases (y :: L),
  {
    
  }
end
-- Q6
-- 5 Points
-- Grading comment:
-- /-
-- prove the theorem below. 
-- hint: do not use induction! use a result we have proven in our homeworks.
-- -/
-- theorem rev_injective: 
--     ∀ L1 L2 : list nat, rev L1 = rev L2 -> L1 = L2
-- Q7
-- 5 Points
-- Grading comment:
-- /-
-- prove the theorem below. 
-- hint: do not use induction! use a result we have proven in our homeworks.
-- -/
-- lemma len_app_commut: 
--     ∀ L1 L2 : list nat, len (app L1 L2) = len (app L2 L1)
-- Q8
-- 22 Points
-- Grading comment:
-- /-
-- consider the functions eleml and subset defined below:
-- -/
def eleml : nat -> list nat -> bool 
  | _ [] := ff 
  | n (x :: L) := if (n = x) then tt else (eleml n L)
def subset : list nat -> list nat -> Prop 
  | [] _ := true
  | (x :: L1) L2 := and (eleml x L2 = tt) (subset L1 L2)
-- Q8.1
-- 5 Points
-- Grading comment:
-- /-
-- prove the lemma below.
-- hint: you don't need induction.
-- -/
lemma subset_drop_head : 
forall L1 L2 : list nat, forall x : nat, 
    subset (x :: L1) L2 -> subset L1 L2 := begin
  intros L1 L2 x h,
  dunfold subset at h,
  cases h,
  {
    assumption
  }
end
-- Q8.2
-- 17 Points
-- Grading comment:
-- /-
-- prove theorem subset_refl. 
-- hint: you will need a lemma that you will discover by generalization. that generalization resembles the one we did for app_L_3_times_failed in 14-code.lean. 
-- -/
lemma help : ∀ (a b : nat) (L1 L2 : list ℕ ), (a = b) ∧ subset L1 L2 -> subset (a :: L1) (b :: L2) := begin
  intros a b L1 L2,

end
theorem subset_refl: forall L : list nat, subset L L :=
begin
  intros,
  induction L with L h ih,
  {
    dunfold subset,
    trivial
  },
  {
    
  }
end
-- Q9
-- 8 Points
-- Grading comment:
-- /-
-- consider the function app_t3 given below:
-- -/
def app_t3 : list nat -> list nat -> list nat -> list nat 
  | list.nil list.nil acc := acc
  | [ ] (b :: L) acc := app_t3 [ ] L (b :: acc)
  | (a :: L) [ ] acc := app_t3 L [ ] (a :: acc)
  | (a :: L1) (b :: L2) acc := app_t3 (a :: L1) [ ] (app_t3 [ ] (b :: L2) acc)
-- /-
-- suppose m3 is a candidate measure function for app_t3. write down the decreasing measure proof obligation(s) for m3.
-- do not define m3, and do not try to prove anything. just write down the proof obligation(s). 
-- -/
