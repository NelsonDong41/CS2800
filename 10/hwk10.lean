-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 10

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Alyssa Mui, Nelson Dong, Justin Pong
-/

/-
Technical instructions: same as in the last homework.

IN THIS HOMEWORK YOU ARE ALLOWED TO USE FUNCTIONAL INDUCTION. (this does NOT imply that you need it). WE WILL CUT POINTS for illegal use of the induction hypothesis in functional induction proofs. 
-/


import .ourlibrary16
import .ourlibraryite


/- HWK10-01: 
Prove the theorem treesize_len given below:
-/

inductive tree : Type 
  | leaf : ℕ → tree 
  | node : ℕ → tree → tree → tree 
--

open tree 

def treesize : tree → ℕ 
  | (leaf x) := 1 
  | (node x t1 t2) := nat.succ (plus (treesize t1) (treesize t2))
--

def tree2list : tree → list ℕ 
  | (leaf x) := [x] 
  | (node x t1 t2) := x :: (app (tree2list t1) (tree2list t2))
--

-- ANSWER:

lemma one : ∀ L1 L2 : list ℕ, len (app L1 L2) = plus (len L1) (len L2) :=
begin
  intros,
  induction L1 with x L Lih,
  {
    dunfold app,
    dunfold len,
    dunfold plus,
    refl,
  },
  {
    dunfold app,
    dunfold len,
    dunfold plus,
    rw succeq,
    assumption
  }
end


theorem treesize_len: ∀ t : tree, treesize t = len (tree2list t) 
  | (tree.leaf x)  := begin
    dunfold treesize,
    dunfold tree2list,
    dunfold len,
    refl,
  end  
  | (tree.node x y z) := begin
    dunfold treesize,
    dunfold tree2list,
    dunfold len,
    rw treesize_len y,
    rw treesize_len z,
    rw succeq,
    have h1 := one (tree2list y) (tree2list z),
    rw h1,
  end




/- HWK10-02: 
Consider the following function:
-/
def list_delete : list ℕ → ℕ → list ℕ 
    | [] _ := []
    | (x :: L) 0 := L 
    | (x :: L) (nat.succ i) := x :: (list_delete L i)
--

example: list_delete [1,2,3] 0 = [2,3] := begin refl, end 
example: list_delete [1,2,3] 1 = [1,3] := begin refl, end 
example: list_delete [1,2,3] 2 = [1,2] := begin refl, end 
example: list_delete [1,2,3] 3 = [1,2,3] := begin refl, end 


/- HWK10-02-1: 
is the following claim true? if so prove it, if not, exhibit a counterexample:
-/
theorem list_delete_len:
  ∀ (L : list ℕ), list_delete L (len L) = L 
-- ANSWER:
| [] := begin
  refl,
end
| (x :: L) := begin
  dunfold len,
  dunfold list_delete,
  rw listeq,
  split,
  refl,
  rw list_delete_len,
end

/- HWK10-02-2: 
is the following claim true? if so prove it, if not, exhibit a counterexample:
-/

theorem list_delete_outofbounds:
  ∀ (L : list ℕ) (i : ℕ), 
    leq (len L) i = tt → list_delete L i = L 
-- ANSWER:
 | [] 0 := begin
    intro h,
    refl,
 end
 | [] (nat.succ x) := begin
    intro h,
    dunfold list_delete,
    refl,
 end
 | (x :: L) 0 := begin
    intro h,
    dunfold list_delete,
    contradiction,
 end
 | (x :: L) (nat.succ i) := begin
    intros h,
    have h1 := list_delete_outofbounds L i h,
    dunfold list_delete,
    rw listeq,
    split,
    refl,
    assumption,
 end



/- HWK10-03: 

prove the following interesting result about functions on booleans. 

HINT: follow the method in "how not to lose your bool cases", 17-code.lean 
-/

theorem bool_fn_applied_thrice: 
    forall (f : bool -> bool) (b : bool), f (f (f b)) = f b
-- ANSWER:
:= begin
  intros,
  have h : ∀ b : bool, (f b) = tt ∨ (f b) = ff := begin
    intro b,
    cases (f b),
    right, refl,
    left, refl,
  end,
  have h2 := h b,
  cases h2,
  {
    rw h2,
    have h3 := h tt,
    have h4 := h ff,
    cases h3,
    {
      rw h3,
      rw h3,
    },
    {
      rw h3,
      cases h4,
      {
        assumption,
      },
      {
        cases b,
        {
          rw h2 at h4,
          contradiction,
        },
        {
          rw h2 at h3,
          contradiction,
        }
      }
    }
  },
  {
    rw h2,
    have h3 := h ff,
    have h4 := h tt,
    cases h3,
    {
      rw h3,
      cases h4,
      {
        cases b,
        {
          rw h2 at h3,
          contradiction,
        },
        {
          rw h2 at h4,
          contradiction,
        }
      },
      {
        assumption,
      }
    },
    {
      rw h3,
      rw h3,
    }
  }
end


/- HWK10-04: 
define the function "eleml" which takes a nat x and a list of nats L and returns bool tt if x is in L and bool ff otherwise. 

as usual, all given tests must pass. 

also make sure that your eleml satisfies the lemma given below. prove that it does. 
-/
-- ANSWER:
def eleml : nat → list nat → bool 
  | _ [] := ff
  | x (y :: L) := orb (eqb x y) (eleml x L)
-- 

example: eleml 3 [] = ff := begin refl, end 
example: eleml 0 [1,2,3] = ff := begin refl, end 
example: eleml 1 [1,2,3] = tt := begin refl, end
example: eleml 2 [1,2,3] = tt := begin refl, end
example: eleml 3 [1,2,3] = tt := begin refl, end


lemma three : ∀ L1 : list ℕ , app L1 [] = app [] L1 :=
begin
  intros,
  dunfold app,
  induction L1,
  dunfold app,
  refl,
  dunfold app,
  rw listeq,
  split,
  refl,
  assumption
end

lemma eleml_app: ∀ x : ℕ, ∀ L1 L2 : list ℕ, 
  eleml x (app L1 L2) = (eleml x L1) || (eleml x L2)
| x [] [] := begin
  dunfold app,
  dunfold eleml,
  refl,
end
| x [] (y :: L) := begin
  dunfold app,
  split,
end
| x (y :: L) [] := begin
  dunfold app,
  dunfold eleml,
  rw three,
  dunfold app,
  have h : (eqb x y = tt) ∨ (eqb x y = ff) := begin
    cases (eqb x y),
    right, refl,
    left, refl,
  end,
  cases h,
  {
    rw h,
    dunfold orb,
    trivial,
  },
  {
    rw h,
    dunfold orb,
    have h2 : (eleml x L = tt) ∨ (eleml x L = ff) := begin
      cases (eleml x L),
      right, refl,
      left, refl,
      end,
    cases h2,
    repeat {
      rw h2,
      trivial,
    },
  }
end
| x (y :: L) (z :: L2) := begin
  dunfold app,
  dunfold eleml,
  have h : (eqb x y = tt) ∨ (eqb x y = ff) := begin
    cases (eqb x y),
    right, refl,
    left, refl,
  end,
  have h2 : (eqb x z = tt) ∨ (eqb x z = ff) := begin
    cases (eqb x z),
    right, refl,
    left, refl,
  end,
  have h3 := eleml_app x L (z :: L2),
  rw h3,
  cases h,
  {
    rw h,
    rw orb,
    trivial,
  },
  {
    rw h,
    rw orb,
    rw orb,
    dunfold eleml,
    cases h2,
    repeat {
      rw h2,
    }
  }
end



/- HWK10-05: 
define the function "removedups" which takes a list of nats L and removes all duplicate elements from it. 

as usual, all given tests must pass: complete the proofs of the ones given below.  

also make sure that your removedups satisfies the lemma given below. prove that it does. 
-/
-- ANSWER:
def removedups : list nat → list nat 
  | [] := []
  | (x :: L) := ite (eleml x L = tt) (removedups L) (app [x] (removedups L))
--

example: removedups [] = [] := begin refl, end 
example: removedups [1,2,3] = [1,2,3] := begin refl, end 
example: removedups [1,2,3,3] = [1,2,3] := begin refl, end 
example: removedups [2,2,1,1,3,3] = [2,1,3] := begin refl, end 
example: removedups [2,1,1,2,3,2] = [1,2,3] 
        ∨ removedups [2,1,1,2,3,2] = [1,3,2] 
        ∨ removedups [2,1,1,2,3,2] = [2,1,3] 
:= begin
  right, left, refl,
end 

lemma eqb_x_y_iff_x_eq_y : ∀ (x y : ℕ), eqb x y = tt ↔ x = y
  | 0 0 := begin
    split,
    repeat {
      intros,
      trivial,
    }
  end
  | 0 (nat.succ y) := begin
    split,
    {
      intro h,
      rw eqb at h,
      contradiction,
    },
    {
      intro h,
      contradiction,
    }
  end
  | (nat.succ x) 0 := begin
    split,
    {
      intro h,
      rw eqb at h,
      contradiction,
    },
    {
      intro h,
      contradiction,
    }
  end
  | (nat.succ x) (nat.succ y) := begin
    split,
    {
      intro h,
      rw eqb at h,
      rw succeq,
      have h2 := eqb_x_y_iff_x_eq_y x y,
      rw <- h2,
      assumption,
    },
    {
      intro h,
      rw eqb,
      rw succeq at h,
      have h2 := eqb_x_y_iff_x_eq_y x y,
      rw h2,
      assumption,
    }
  end


lemma eleml_removedups: ∀ x : ℕ, ∀ L : list ℕ, 
  eleml x (removedups L) = eleml x L  
  | x [] := begin
    dunfold removedups,
    refl
  end
  | x (y :: L) := begin
    dunfold removedups,
    have h : (eleml y L = tt) ∨ (eleml y L = ff) := begin
      cases (eleml y L),
      right, refl,
      left, refl,
    end,
    cases h,
    {
      rw h,
      rw itetrue,
      rw eleml,
      have h2 := eleml_removedups x L,
      rw h2,
      have h3 : (eqb x y = tt) ∨ (eqb x y = ff) := begin
        cases (eqb x y),
        right, refl,
        left, refl,
      end,
      cases h3,
      {
        rw h3,
        rw orb,
        rw <- h,
        have h4 := eqb_x_y_iff_x_eq_y x y,
        rw h4 at h3,
        rw h3,
      },
      {
        rw h3,
        rw orb,
      },
      refl,
    },
    {
      rw h,
      rw itefalse,
      dunfold app,
      dunfold eleml,
      have h2 := eleml_removedups x L,
      rw h2,
      trivial,
    }
  end



/-
we are now starting to build our SAT solver!

we first introduce our boolean expressions, with a small change: vars are now constructed with nats. we can discuss why in class. 
-/

inductive binop : Type 
  | and : binop 
  | or  : binop 
  | imp : binop 
  | iff : binop 
  | xor : binop 
  /-
  invalid binder, identifier expected
  -/
  
--

inductive bx : Type 
  | bxconst : bool → bx 
  | bxvar : nat → bx 
  | bxnot : bx → bx 
  | bxbin : binop → bx → bx → bx   -- binary operator 
--

open bx 

-- you will probably need to use this simplification function later
def bx_and_simp : bx → bx 
  | (bxconst b) := (bxconst b) 
  | (bxvar n) := (bxvar n)
  | (bxnot e) := (bxnot e)
  | (bxbin binop.and (bxconst tt) e2) := bx_and_simp e2 
  | (bxbin binop.and e1 (bxconst tt)) := bx_and_simp e1 
  | (bxbin binop.and (bxconst ff) e2) := (bxconst ff)
  | (bxbin binop.and e1 (bxconst ff)) := (bxconst ff)
  | (bxbin o e1 e2) := bxbin o (bx_and_simp e1) (bx_and_simp e2)
--

/-
notation is supposed to make your life easier. you can use the definitions below (for older or more recent LEAN versions). 

if notation does not work for you, you can remove it, but you need to adapt all subsequent tests! 
-/

-- local notation `T` := bx.bxconst tt
-- local notation `F` := bx.bxconst ff
-- local notation `x` n := bx.bxvar n
-- local notation `~` a := bx.bxnot a
-- local notation  a ` => ` b := bx.bxbin binop.imp a b
-- local notation  a ` ⬝ ` b := bx.bxbin binop.and a b
-- local notation  a ` + ` b := bx.bxbin binop.or a b
-- local notation  a ` <=> ` b := bx.bxbin binop.iff a b
-- local notation  a ` ⊕ ` b := bx.bxbin binop.xor a b
--or in recent LEAN versions:
local notation (name := b_const_t) `T` := bx.bxconst tt
local notation (name := b_const_f) `F` := bx.bxconst ff
local notation (name := b_var) `x` n := bx.bxvar n
local notation (name := b_not) `~` a := bx.bxnot a
local notation (name := b_imp)  a ` => ` b := bx.bxbin binop.imp a b
local notation (name := b_and)  a ` ⬝ ` b := bx.bxbin binop.and a b
local notation (name := b_or)  a ` + ` b := bx.bxbin binop.or a b
local notation (name := b_iff)  a ` <=> ` b := bx.bxbin binop.iff a b
local notation (name := b_xor)  a ` ⊕ ` b := bx.bxbin binop.xor a b


-- a boolean expression written without notation:
#check bx.bxbin binop.and (bx.bxbin binop.or (bx.bxvar 1) (bx.bxvar 2)) (bx.bxbin binop.imp (bx.bxvar 1) (bx.bxnot (bx.bxvar 2)))
-- the same boolean expression written with notation:
#check ((x 1) + x 2) ⬝ (x 1 => ~x 2) 



open bx 



/- HWK10-06: 

define a function bxvars : bx → list nat, which takes as input a bx e and returns the list of all variables (variable IDs) appearing in e. the list should not have duplicates. 

as usual, you are allowed to define your own helper functions. 

as usual all given tests must pass. 

your bxvars must also satisfy all the lemmas given below: prove them. hint: you shouldn't need induction for any of these lemmas. use lemmas, including those proven earlier in this homework. 
-/

-- ANSWER:


def bxvars : bx -> list ℕ
  | (bx.bxconst n) := []
  | (bx.bxvar n) := [n]
  | (bx.bxnot n) := bxvars n
  | (bx.bxbin binop n y) := removedups (app (bxvars n) (bxvars y))
   
example: bxvars T = [] := begin refl, end 
example: bxvars F = [] := begin refl, end 
example: bxvars ((F + T) ⬝ (F => ~F)) = [] 
:= begin refl, end 
example: bxvars (((x 1) + x 2) ⬝ (x 1 => ~x 2)) = [1,2] 
:= begin refl, end 
example: bxvars ((T + x 2) ⬝ (x 1 => ~x 2)) = [1,2] 
:= begin refl, end 



lemma bxvars_not: ∀ e : bx, bxvars (bxnot e) = bxvars e 
  | (bxconst y) := begin 
    dunfold bxvars,
    refl
  end 
  | (bxvar y) := begin
    dunfold bxvars,
    refl,
  end
  | (bxnot y) := begin
    dunfold bxvars,
    refl,
  end
  | (bxbin binop n y) := begin
    dunfold bxvars,
    refl,
  end


lemma orb_false: ∀ b : bool, ((orb b ff) = ff) → (b = ff)
:= begin
  intros b h,
  cases b,
  refl,
  contradiction,
end

lemma eqb_eq: ∀ n m : ℕ , eqb n m = ff → n ≠ m
:= begin
  intros n,
  induction n with n ih, {
    intros m h h1,
    cases m, {
      rw eqb at h,
      trivial,
    },
    {
      trivial,
    }
  },
  {
    intros m h h1,
    cases m, {
      trivial,
    },
    {
      rw eqb at h,
      rw succeq at h1,
      have h2 := ih m,
      have h3 := h2 h,
      contradiction,
    }
  }
end

lemma elem_not_in: ∀ n m : ℕ , (eleml n [m] = ff) → n ≠ m
:= begin
  intros n m,
  dunfold eleml,
  intros h h1,
  have h2 := orb_false (eqb n m),
  have h3 := h2 h,
  have h4 := eqb_eq n m,
  have h5 := h4 h3,
  contradiction,
end

lemma eleml_bxvars_var_ff: 
∀ n m : ℕ, ∀ e : bx, ∀ o : binop,
  eleml n (bxvars (bxbin o (bxvar m) e)) = ff
    → n ≠ m 
  | n m e o := begin
    intros h,
    rw bxvars at h,
    rw eleml_removedups at h,
    rw eleml_app at h,
    rw bor_eq_false_eq_eq_ff_and_eq_ff at h,
    cases h with h1 h2,
    rw bxvars at h1,
    have h3 := elem_not_in n m,
    have h4 := h3 h1,
    exact h4,
end


lemma eleml_bxvars_not_ff: 
∀ n : ℕ, ∀ e1 e2 : bx, ∀ o : binop,
  eleml n (bxvars (bxbin o (bxnot e1) e2)) = ff
    → eleml n (bxvars (bxbin o e1 e2)) = ff 
  | n e1 e2 o := begin
    dunfold bxvars,
    intro h,
    assumption,
  end  

lemma eleml_bxvars_binop_ff: 
∀ e1 e2 : bx, ∀ o : binop, ∀ n : ℕ, 
  eleml n (bxvars (bxbin o e1 e2)) = ff 
    → (eleml n (bxvars e1)) = ff 
        ∧ 
      (eleml n (bxvars e2)) = ff 
  | e1 e2 o n := begin
    dunfold bxvars,
    intro h,
    rw eleml_removedups at h,
    rw eleml_app at h,
    rw bor_eq_false_eq_eq_ff_and_eq_ff at h,
    cases h, 
    split, {
      exact h_left,
    },
    {
      exact h_right,
    }
end



/- HWK10-07: 

define a function bxsubst : bx → nat → bool → bx, which takes as input a bx e, a nat n, and a bool b, and returns a new bx f, such that all occurrences of variable with ID n in e are replaced by (bxconst b) in f. if e does not contain variable with ID n, then f is the same as e. 

as usual, all tests given below must pass. your bxsubst also needs to satisfy theorem bxsubst_no_change given below. prove this. hint: use induction on the bx e, and some of the lemmas you proved above. 
-/

-- ANSWER:
def bxsubst : bx → nat → bool → bx 
  | (bx.bxconst e) n b := (bx.bxconst e)
  | (bx.bxvar e) n b := if e = n then (bx.bxconst b) else (bx.bxvar e)
  | (bx.bxnot e) n b:= (bx.bxnot (bxsubst e n b))
  | (bx.bxbin binop e1 e2) n b := bx.bxbin binop (bxsubst e1 n b) (bxsubst e2 n b)
--

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 1 tt 
=  ((T + x 2) ⬝ (T => ~x 2))
:= begin refl, end

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 1 ff 
=  ((F + x 2) ⬝ (F => ~x 2))
:= begin refl, end

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 2 tt 
= (((x 1) + T) ⬝ ((x 1) => ~T))
:= begin refl, end

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 3 tt 
= (((x 1) + x 2) ⬝ (x 1 => ~x 2))
:= begin refl, end

theorem bxsubst_no_change: ∀ e : bx, ∀ n : ℕ, ∀ b : bool,
  eleml n (bxvars e) = ff → bxsubst e n b = e 
  | (bxconst c) n b := begin
    intros h,
    rw bxsubst,
    end
  | (bxvar v) n b := begin
    intros h,
    rw bxsubst,
    rw bxvars at h,
    rw itefalse, {
      intros h1,
      have h2 := elem_not_in n v,
      have h3 := h2 h,
      rw eq_comm at h1,
      contradiction,
    }
    end
  | (bxnot b1) n b := begin
      intros h,
      dunfold bxsubst,
      dunfold bxvars at h,
      have h1 := bxsubst_no_change b1 n b,
      have h2 := h1 h,
      rw h2,  
    end
  | (bxbin op e1 e2) n b := begin
    intros h,
    dunfold bxsubst,
    dunfold bxvars at h,
    rw eleml_removedups at h,
    rw eleml_app at h,
    rw bor_eq_false_eq_eq_ff_and_eq_ff at h,
    cases h,
    have h1 := bxsubst_no_change e1 n b,
    have h2 := h1 h_left,
    have h3 := bxsubst_no_change e2 n b,
    have h4 := h3 h_right,
    rw h2,
    rw h4,
    end





/- HWK10-08: 

define a function bxeval : bx → bool, which takes as input a bx e without any variables, and evaluates it to tt or ff, according to the usual semantics of propositional logic. 

if e has variables, they should be evaluated to ff. 

as usual, all tests given below must pass. 

also prove that your bxeval satisfies the theorem bxeval_not given below. 
-/

-- ANSWER: 
def bxeval : bx → bool 
  | (bxconst e) := e
  | (bxvar e) := ff
  | (bxnot e) := ite ((bxeval e) = tt) ff tt
  | (bxbin binop.imp a b) := (bxeval (bxnot a)) || (bxeval b) 
  | (bxbin binop.and a b) := (bxeval a) && (bxeval b)
  | (bxbin binop.or a b) := (bxeval a) || (bxeval b)
  | (bxbin binop.iff a b) := (bxeval a) = (bxeval b)
  | (bxbin binop.xor a b) := ((bxeval (bxnot a)) && (bxeval b)) || ((bxeval a) && (bxeval (bxnot b)))
--

example: bxeval F = ff := begin 
  rw bxeval,
end
example: bxeval T = tt := begin
  rw bxeval,
end

example: bxeval ((F + T) ⬝ (F => ~T)) = tt 
:= begin 
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw itefalse,
  rw itetrue,
  refl,
  refl,
  trivial,
end

example: bxeval ((F + T) ⬝ (T => ~T)) = ff 
:= begin
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw itetrue,
  refl,
  refl,
end

example: bxeval (((x 1) + T) ⬝ (x 1 => ~T))  = tt 
:= begin
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw itefalse,
  rw itetrue,
  refl,
  refl,
  trivial,
end

example: bxeval (((x 1) + x 2) ⬝ (x 1 => ~x 2)) = ff 
:= begin
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw bxeval,
  rw itefalse,
  refl,
  trivial,
end

theorem bxeval_not: ∀ e : bx, bxeval e = tt ↔ bxeval (bxnot e) = ff 
  | e := begin
    split,
    {
      intro h,
      rw bxeval,
      rw h,
      rw itetrue,
      refl,
    },
    {
      intro h,
      rw bxeval at h,
      have h2 : (bxeval e = tt) ∨ (bxeval e = ff) := begin
        cases (bxeval e),
        right, refl,
        left, refl,
      end,
      cases h2,
      {
        rw h2 at h,
        rw itetrue at h,
        assumption,
        refl,
      },
      {
        rw h2 at h,
        rw itefalse at h,
        contradiction,
        trivial,
      }
    }
  end


/-
a brute-force way to solve the SAT problem is to check all possible assignments: if we find one that satisfies the formula, the formula is SAT. otherwise it's UNSAT. recall that an assignment is a function that maps each variable to the formula to either T or F (true or false). if the formula has k variables, there are 2^k possible assignments. 

assignments can be partial, meaning that some, but not all, of the variables of a given formula have been assigned values. 

we can represent (complete or partial) assignments as bx's. an assignment can be represented as a special bx which is a conjunction of literals. a literal is either a variable or a negated variable. for example, these are some assignments represented as bx's: 
-/

-- x1, x2 and x3 are all true: 
#check (x 1) ⬝ (x 2) ⬝ (x 3)

-- x1 and x2 are true, x3 is false: 
#check (x 1) ⬝ (x 2) ⬝ (~x 3)

-- x1, x2 and x3 are all false: 
#check (~x 1) ⬝ (~x 2) ⬝ (~x 3)




/- HWK10-09: 

define a function

   sath : bx → list nat → bx → (bool × bx) 

sath is a helper to the main sat function. sath takes as inputs:
  - a bx e 
  - a list of nats (variable IDs) L: L is the list of unassigned variables of e. 
  - a bx g: g is the tentative partial assignment that we have so far. 
  
if e is SAT, then sath returns a pair (tt, d) where d is a satisfying assignment of e. otherwise, sath returns the pair (ff, (bxconst ff)). 

you can follow the following logic:
  - if L is empty, it means all variables have been assigned and e has no more variables. then we can just evaluate e. 

  - if L has at least one variable, say x, then:
    - assign x to (bxconst tt), and check recursively if the new formula obtained by substituting x by T in e is SAT. (remember also to update the assignment passed to the recursive call of sath!).  if the new formula is SAT, you are done!
    - if not, try the assignment where x is assigned to (bxconst ff) instead. if this works, you're done! if not, the formula is UNSAT. 

all tests given below must pass. 

you must also prove that your sath function satisfies the theorems given below. 
-/

-- ANSWER: 

def sath : bx → list nat → bx → (bool × bx) 
  | e [] g := ite (bxeval e = tt) (tt, g) (ff, (bxconst ff))
  | e (n :: L) g := ite ((sath (bx_and_simp (bxsubst e n tt)) L (g ⬝ (x n))).fst = tt) (sath (bx_and_simp(bxsubst e n tt)) L (g ⬝ (x n))) (sath (bx_and_simp (bxsubst e n ff)) L (g ⬝ (~x n)))
--

example: sath F [] F = (ff, F) := begin 
  rw sath, 
  rw bxeval,
  rw itefalse,
  trivial,
end
example: sath T [] T = (tt, T) := begin 
  rw sath,
  rw bxeval,
  rw itetrue,
  refl,
end
example: ∀ a : bx, sath T [] a = (tt, a) := begin 
  intro, 
  rw sath,
  rw bxeval,
  rw itetrue,
  refl,
end

theorem sath_bxeval_tt: ∀ e a : bx, 
  bxvars e = [] → bxeval e = tt → sath e [] a = (tt, a) 
  | e a := begin
    intros subh1 subh2,
    rw sath,
    rw subh2,
    rw itetrue,
    refl,
  end          


theorem sath_bxeval_ff: ∀ e a : bx, 
  bxvars e = [] → bxeval e = ff → sath e [] a = (ff, (bxconst ff)) 
  | e a := begin
    intros subh1 subh2,
    rw sath,
    rw subh2,
    rw itefalse,
    trivial,
  end      



/- HWK10-10: 

with the help of sath, write the main "sat" function. sat takes as input a bx e and returns a pair (bool × bx):

  - if e is satisfiable, then sat returns a pair (tt, g), where g is a satisfying assignment of e. 

  - if e is unsatisfiable, then sat returns the pair (ff, (bxconst ff)). 

also write the following functions, derivatives of "sat":

  - the function satyesno: bx → bool, which takes a bx e and returns tt if e is SAT and ff otherwise. use the output of sat and ".fst" to extract the first element of a pair (see 03-code.lean). 

  - the function satasgn: bx → bx, which takes a bx e and returns a satisfying assignment of e if e is SAT and (bxconst ff) otherwise. use the output of sat and ".snd" to extract the second element of a pair (see 03-code.lean). if e is SAT, make sure the satisfying assignment that you return doesn't have any redundant "T ⬝" part, otherwise your tests below will fail. hint: use bx_and_simp to simplify. 

  - the function valid: bx → (bool × bx), which takes a bx e and checks whether e is valid (see 07-propositional-logic.pdf if you don't remember what that means). "valid" should return (tt, (bxconst tt)) if e is valid. otherwise it should return (ff, g), where g is a falsifying assignment, i.e., an assignment that makes e false. 


all tests given below must pass. HOWEVER, NOTE: the given tests are far from being exhaustive. the satisfiable formulas we use have only one satisfying assignment, so that no matter how you implement your own solver, the answer in those cases is unique. 

write more tests on your own to make sure your SAT solver is correct!
-/

-- ANSWERS:

-- the main SAT solver functions:

def sat : bx → (bool × bx)
  | e := (sath e (bxvars e) (bxconst tt))


-- yes/no version
def satyesno : bx -> bool 
  | e := (sat e).fst

-- the assignment returned by sat:
def satasgn : bx -> bx
  | e := bx_and_simp (sat e).snd

-- check validity and return a falsifying assignment if not valid: 
def valid : bx -> (bool × bx)
  | e := ite ((satyesno (bxnot e)) = tt) (ff, satasgn (bxnot e)) (tt, (bxconst tt))
 
example: satasgn F = F := begin
  dunfold satasgn, 
  dunfold sat,
  dunfold bxvars, 
  dunfold sath,
  rw bxeval,
  rw itefalse,
  {
    dunfold bx_and_simp,
    refl,
  },
  {
    trivial,
  }
end
example: satasgn T = T := begin 
  dunfold satasgn,
  dunfold sat,
  dunfold bxvars,
  dunfold sath,
  rw bxeval,
  rw itetrue,
  {
    dunfold bx_and_simp,
    refl,
  },
  {
    refl,
  }

end
example: satasgn (T + F) = T := begin
  dunfold satasgn,
  dunfold sat,
  dunfold bxvars,
  dunfold app,
  dunfold removedups,
  dunfold sath,
  rw itetrue,
  {
    rw bx_and_simp
  },
  {
    rw bxeval,
    rw bxeval,
    rw bxeval,
    trivial,
  }
end
example: satasgn (T ⬝ F) = F := begin 
  dunfold satasgn,
  dunfold sat,
  dunfold bxvars,
  dunfold app,
  dunfold removedups,
  dunfold sath,
  rw itefalse,
  {
    rw bx_and_simp,
  },
  {
    rw bxeval,
    rw bxeval,
    rw bxeval,
    trivial,
  }
end

example: satasgn ((x 1) ⬝ (x 2) ⬝ (x 3)) = (((x 1) ⬝ x 2) ⬝ (x 3))
:= begin
  -- dunfold satasgn,
  -- dunfold sat,
  -- dunfold bxvars,
  -- dunfold app,
  -- dunfold removedups,
  -- dunfold app,
  -- dunfold eleml,
  -- dunfold eqb,
  -- dunfold orb,
  -- rw itefalse,
  -- {
  --   rw itefalse,
  --   {
  --     dunfold app,
  --     dunfold removedups,
  --     dunfold app,
  --     dunfold eleml,
  --     dunfold eqb,
  --     dunfold orb,
  --     rw itefalse,
  --     {
  --       rw itefalse,
  --       {
  --         rw itefalse,
  --         {
  --           rw sath,
  --         }
  --       }
  --     }
  --   }
  -- }
  refl,
end

example: satasgn (~((x 1) + (x 2) + (x 3))) = (((~x 1) ⬝ ~x 2) ⬝ (~x 3))
:= begin refl, end

#reduce satasgn ((x 1) => x 2) <=> ((~x 1) + x 2)
example: satasgn (((x 1) => x 2) <=> ((~x 1) + x 2))

example: satyesno (((x 1) ⊕ (x 2)) ⬝ ((x 1) <=> (x 2))) 
= ff := begin refl, end

example: satyesno  
(
  ((x 1) => x 2) <=> ((~x 1) + x 2)
) 
= tt := begin 
  refl,
end 

example: satyesno  
(((x 1) <=> (x 2)) ⊕ ((x 1) <=> (x 2))) = ff := begin refl, end

-- proof for example became too long and using refl doesn't work
#reduce satyesno (
  ((x 1) <=> (x 2)) ⊕ ((x 1) <=> (x 2))
) 

example: valid 
(
  ((x 1) => x 2) <=> ((~x 1) + x 2)
) 
= (tt, T) := begin 
  refl,
end 

example: valid 
(
  ((~x 1) + x 1)
) 
= (tt, T) := begin 
  dunfold valid,
  dunfold satyesno,
  dunfold satasgn,
  dunfold sat,
  dunfold bxvars,
  dunfold app,
  dunfold removedups,
  dunfold eleml,
  dunfold eqb,
  dunfold orb,
  dunfold app,
  dunfold satyesno,
  dunfold sat,
  dunfold bxvars,
  dunfold app,
  dunfold removedups,
  dunfold app,
  dunfold eleml,
  dunfold eqb,
  dunfold orb,
end 

example: valid 
(
  ((~x 1) + x 2)
) 
= (ff, (x 1) ⬝ ~x 2) := begin refl, end 

example: valid 
(
  ((x 1) ⊕ x 2) <=> ~((x 1) <=> x 2)
) 
= (tt, T) := begin refl, end 

example: valid (
  ((~x 1) + x 2) ⬝ (x 3)
) = (ff, x 1 ⬝ x 2 ⬝ ~x 3) := begin refl, end

example : valid (
  ((x 1) ⊕ x 2) <=> ~((x 1))
) = (ff, ~x 2 ⬝ x 1) := begin refl, end

example : valid ((x 1) ⬝ ~x 2 <=> ((x 1) ⊕ x 2)) = (ff, ~x 1 ⬝ x 2) := begin refl, end


example : sat ((x 1) ⬝ ~x 2 <=> ((x 1) ⊕ x 2)) = (tt, T ⬝ x 1 ⬝ x 2) := begin sorry, end

#reduce sat ((x 1) ⬝ ~x 2 <=> ((x 1) ⊕ x 2))

example : sat ((x 1) ⬝ ~x 2 <=> ((x 1) ⊕ x 2)) = (tt, T ⬝ x 1 ⬝ x 2) := begin sorry, end

example : sat ((~x 1) + x 1) = (tt, T ⬝ x 1) := begin sorry, end
#reduce sat ((~x 1) + x 1)

example : sat ((~x 1) ⬝ (x 2) ⊕ (x 3) + (x 4)) = (tt, T ⬝ ~x 1 ⬝ x 2 ⬝ ~x 3 ⬝ ~x 4):= begin sorry, end
#reduce sat ((~x 1) ⬝ (x 2) ⊕ (x 3) + (x 4))