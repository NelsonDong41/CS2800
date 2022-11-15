-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 9

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Alyssa Mui, Justin Pong, Nelson Dong
-/

/-
Technical instructions: same as in the last homework.

in particular, you are still NOT allowed to use functional induction in this homework. 
-/


import .ourlibrary11
import .ourlibrary12 
import .ourlibrary16 
import .ourlibraryite


-- GENERAL HINT FOR THIS AND FOLLOWING HOMEWORKS: IN SEVERAL PROBLEMS YOU WILL NEED TO DELAY INTRODUCTIONS (c.f. 16-code.lean)


/- HWK09-01: 
prove each of the following theorems. 

think: which ones need induction?
-/

theorem eqb_succ_inj: 
∀ x y : ℕ, eqb (nat.succ x) (nat.succ y) = tt → eqb x y = tt 
:= begin
-- ANSWER:
  intros x y,
  dunfold eqb, 
  intros h,
  exact h,
end


theorem eqb_refl: ∀ x : ℕ, eqb x x = tt 
:= begin
-- ANSWER:
  intros x,
  induction x with x ih,
  {
    dunfold eqb,
    refl,
  },
  {
    dunfold eqb,
    exact ih,
  }
end

theorem leq_x_succ_x: ∀ x : ℕ, leq x (nat.succ x) = tt 
:= begin
-- ANSWER:
  intros x,
  induction x with x ih, {
    rw leq,
  },
  {
    dunfold leq,
    exact ih,
  }
end


theorem eqb_eq_zero: ∀ x : ℕ, eqb x 0 = tt → x = 0 
:= begin
-- ANSWER:
  intros x h,
  cases x, {
    refl,
  },
  {
    rw eqb at h,
    contradiction,
  }
end


/- HWK09-02: 
prove the following theorem:
-/

lemma lem2 : ∀ y : ℕ , eqb y y = tt :=
begin
  intros,
  induction y,
  {
    dunfold eqb,
    refl,
  },
  {
    dunfold eqb,
    assumption
  }
end

theorem eqb_iff_eq: ∀ x y : ℕ, eqb x y = tt ↔ x = y 
:= begin
  intros,
  split,
  {
    intro h,
    revert x,
    induction y,
    {
      intros,
      cases x,
      {
        refl
      },
      {
        dunfold eqb at h,
        contradiction
      }
    },
    {
      intros,
      cases x,
      {
        dunfold eqb at h,
        contradiction
      },
      {
        dunfold eqb at h,
        have h1 := y_ih x,
        have h2 := h1 h,
        rw succeq,
        assumption
      }
    }
  },
  {
    intro h,
    revert y,
    induction x,
    {
      intros,
      rw <- h,
      dunfold eqb,
      refl
    },
    {
      intros,
      rw h,
      have h2 := lem2 y,
      assumption
    }
  }
end


/- HWK09-03:
 prove the following:
-/

lemma lemma3 : ∀ x y : ℕ, (plus x y).succ.succ = plus x.succ y.succ :=
begin
  intros,
  cases x,
  {
    cases y,
    repeat {
      refl,
    }
  },
  {
    cases y,
    repeat {
      induction x with x ih,
      {
        refl,
      },
      {
        dunfold plus,
        dunfold plus at ih,
        rw ih,
      }
    }
  }
end

theorem double_plus: ∀ x : ℕ, double x = plus x x 
-- ANSWER: 
:= begin
  intros,
  induction x with x ih,
  {
    dunfold plus,
    dunfold double,
    refl
  },
  {
    dunfold double,
    rw ih,
    have h3 := lemma3 x x,
    assumption
  }
end



/- HWK09-04:
 prove that our mult is associative. 
-/
-- ANSWER: 

lemma mult_dist  : ∀ x y z : ℕ, mult (plus x y) z = plus (mult x z) ( mult y z ) :=
begin
  intro x,
  induction x with x ih,
  {
    intros,
    dunfold plus,
    dunfold mult,
    dunfold plus,
    refl
  },
  {
    intros,
    dunfold plus,
    dunfold mult,
    have h1 := ih y z,
    rw h1,
    rw plus_assoc,
  }
end

theorem mult_assoc: ∀ x y z : ℕ, mult x (mult y z) = mult (mult x y) z 
:= begin
  intro x,
  induction x with x ih,
  {
    revert,
    dunfold mult,
    intros,
    refl,
  },
  {
    intros,
    dunfold mult,
    rw ih y z,
    rw mult_dist,
  }
end


/- HWK09-05:
 prove the following WITHOUT USING INDUCTION:

 hint: rewrite the goal several times, using the definition of square and the commutativity and associatity laws of mult. 
-/
def square (n : ℕ) := mult n n


lemma square_mult : 
    forall n m, square (mult n m) = mult (square n) (square m) 
:= begin
-- ANSWER:
  intros n m,
  dunfold square,
  cases n, {
    dunfold mult,
    refl,
  },
  {
    rw mult_assoc,
    rw mult_assoc,
    rw mult_commut (mult n.succ m),
    have h1 := mult_assoc n.succ n.succ m,
    rw h1,
  }
end



/- HWK09-06:

earlier, we saw different ways to define "plus". we will revisit one of those definitions in this problem. 

suppose we define plus in this way:
-/

def plus4: nat -> nat -> nat 
  | x nat.zero := x
  | x (nat.succ y) := plus4 (nat.succ x) y   
    -- x + (y+1)  =  (x+1) + y 
--


/- HWK09-06-1:
prove the following: did you need induction? 
-/
theorem plus4_x_zero: ∀ x : ℕ, plus4 x 0 = x 
:= begin 
-- ANSWER:
 intros x, 
 rw plus4,
end 




/- HWK09-06-2:

prove the following:

theorem plus4_zero_x: ∀ x : ℕ, plus4 0 x = x 

hint: use lemma discovery by generalization. 
-/
-- ANSWER:

lemma succ_3: ∀ x y : nat, plus4 y.succ x.succ = plus4 y.succ.succ x
:= begin
  intros x,
  induction x with x ih, {
    intros y,
    rw plus4,
  },
  {
    intros y,
    dunfold plus4,
    refl,
  }
end

lemma succ_2: ∀ x y : nat , (plus4 y x).succ = plus4 y x.succ
:= begin
  intros x,
  induction x with x ih, {
    intros y,
    dunfold plus4,
    refl,
  },
  {
    intros y,
    dunfold plus4,
    have h1 := ih y.succ,
    rw succ_3 at h1,
    exact h1,
  }
end

lemma one_succ: ∀ x y: ℕ , y = 1 -> plus4 y x = x.succ
:= begin
  intros x,
  induction x with x ih, {
    intros y h,
    rw plus4,
    exact h,
  },
  {
    intros y h,
    have h2 := ih y,
    have h3 := h2 h,
    rw <- h3,
    rw ih, {
      rw <- succeq at h3,
      rw succ_2 at h3,
      exact h3,
    },
    {
      exact h,
    }
  }
end

theorem plus4_zero_x: ∀ x : ℕ, plus4 0 x = x 
:= begin
  intros x,
  induction x with x ih, {
    rw plus4,
  },
  {
    dunfold plus4,
    rw one_succ,
    refl,
  }
end





/- HWK09-07: 

prove that all four versions of plus, functions plus1, plus, plus3, and plus4, are equivalent. that is, prove the following three theorems:

theorem plus1_equiv_plus: ∀ x y : nat, plus1 x y = plus x y 

theorem plus_equiv_plus3: ∀ x y : nat, plus x y = plus3 x y

theorem plus3_equiv_plus4: ∀ x y : nat, plus3 x y = plus4 x y

-/

def plus1: nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := (plus1 x (nat.succ y))     
    -- (x+1) + y  =  x + (y+1)   

/-
def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
    -- (x+1) + y  =  (x+y) + 1  
-/

def plus3: nat -> nat -> nat 
  | x nat.zero := x
  | x (nat.succ y) := nat.succ (plus3 x y)   
    -- x + (y+1)  =  (x+y) + 1 

lemma plus1_x_y_succ_equiv_plus1_x_y_succ: ∀ x y : nat, plus1 x y.succ = (plus1 x y).succ
:= begin
  intro,
  induction x with x ih,
  {
    intros,
    refl,
  },
  {
    intro,
    rw plus1,
    rw plus1,
    rw ih,
  }
end

theorem plus1_equiv_plus: ∀ x y : nat, plus1 x y = plus x y 
:= begin
  intros,
  induction x with x ih,
  {
    refl,
  },
  {
    rw plus,
    rw plus1,
    rw <- ih,
    rw plus1_x_y_succ_equiv_plus1_x_y_succ,
  }
end

lemma plus3_0_y_eq_y : ∀ y : nat, plus3 0 y = y
:= begin
  intros,
  induction y with y ih,
  {
    refl,
  },
  {
    rw plus3,
    rw succeq,
    assumption,
  }
end

lemma plus3_y_0_succ_eq_plus3_y_succ_0 : ∀ y : nat, (plus3 y 0).succ = plus3 y.succ 0
:= begin
  intro,
  induction y with y ih,
  {
    refl,
  },
  {
    rw plus3,
    rw plus3,
  }
end

lemma plus3_y_x_succ_eq_plus3_y_succ_x: ∀ x y : nat, (plus3 y x).succ = plus3 y.succ x
:= begin
  intro,
  induction x with x ih,
  {
    intro,
    rw plus3,
    rw plus3
  },
  {
    intro,
    rw plus3,
    rw plus3,
    rw ih,
  }
end

theorem plus_equiv_plus3: ∀ x y : nat, plus x y = plus3 x y
:= begin
  intro,
  induction x with x ih,
  {
    intro,
    rw plus,
    cases y,
    {
      refl,
    },
    {
      rw plus3,
      rw succeq,
      rw plus3_0_y_eq_y,
    }
  },
  {
    intro,
    rw plus,
    rw ih,
    rw plus3_y_x_succ_eq_plus3_y_succ_x,
  }
end

lemma plus4_x_y_succ_eq_plus4_x_y_succ : ∀ y x : nat, (plus4 x y).succ = plus4 x y.succ
:= begin
  intro,
  induction y with y ih,
  {
    intro,
    refl,
  },
  {
    intro,
    rw plus4,
    rw plus4,
    rw ih,
  }
end

theorem plus3_equiv_plus4: ∀ x y : nat, plus3 x y = plus4 x y
:= begin
  intros,
  induction y with y ih,
  {
    refl,
  },
  {
    rw plus3,
    rw ih,
    rw plus4_x_y_succ_eq_plus4_x_y_succ,
  }
end







/- HWK09-08: 
prove the following:
-/


theorem plus_n_n_injective: ∀ n m : ℕ, (plus n n = plus m m) → n = m 
:= begin
-- ANSWER:
  intros n,
  induction n with n ih, {
    intros m h,
    cases m, {
      refl,
    },
    {
      dunfold plus at h,
      contradiction,
    }
  },
  {
    intros m h,
    cases m,
    {
      contradiction
    },
    {
      have h2 := ih m,
      dunfold plus at h,
      rw plus_commut at h,
      dunfold plus at h,
      rw succeq at h,
      rw plus_commut m m.succ at h,
      rw plus at h,
      rw succeq at h,
      rw succeq,
      rw h2 h,
    }
    
  }
end




/- HWK09-09:
Prove the theorem rev_nil_implies_nil:
-/
-- ANSWER: 

lemma app_nil: ∀ (L1 : list nat) (x : ℕ ), app L1 [x] = [] → false
:= begin
  intros L x h,
  cases L with L x ih, repeat {
    trivial,
  },
end

theorem rev_nil_implies_nil: ∀ L : list nat, rev L = [] → L = [] 
:= begin
  intros L h,
  rw <- h,
  cases L with x L h,
  {
    dunfold rev,
    refl,
  },
  {
    dunfold rev,
    dunfold rev at h,
    rw h,
    have h1 := app_nil (rev L) x,
    have h2 := h1 h,
    contradiction
  }
end




/- HWK09-10: 

for the function rl given below, prove the theorem

theorem rl_L_len_L: ∀ L : list ℕ, rl L (len L) = L 

hint: you need lemmas. one of them relates rl, app, and len. discover that lemma by generalization. 
-/

def rl : list ℕ → ℕ → list ℕ 
 | [] 0 := []
 | [] (nat.succ n) := [] 
 | (x :: L) 0 := (x :: L)
 | (x :: L) (nat.succ n) := rl (app L [x]) n 
--

-- ANSWER:

theorem rl_L_len_L: ∀ L : list ℕ, rl L (len L) = L 
:= begin
  intros,
  induction L with x L ih,
  {
    dunfold len,
    refl,
  },
  {
    dunfold len,
    dunfold rl,
    
  }
end





/- HWK09-11: 

we are now strong enough magicians to start proving the correctness of isort! in this homework we will prove the first part, namely that isort always produces sorted lists. 

the isort implementation is given in ourlibrary16.lean: 
-/

#check insrt 
#check isort 

/-
for this problem, you can choose between two options:

  - option A: prove theorem isort_sortedp, which uses sortedp 
  
      theorem isort_sortedp:  ∀ L : list ℕ, sortedp (isort L)

  or

  - option B: prove theorem isort_sortedb, which uses sortedb

      theorem isort_sortedb:  ∀ L : list ℕ, sortedb (isort L) = tt 


you ONLY HAVE TO PROVE ONE OF THEM! but feel free to prove both if you like! each of them is educational in its own way, and we will review both of them later in class. 

if you prove only one of them (this is fine) we recommend that you comment-out the definition of sorted that you DON'T want to use, so that you don't use it by accident. 

you allowed to use any of the lemmas in our lecture notes from the LEAN library, and in particular the two lemmas below:

#check band_eq_false_eq_eq_ff_or_eq_ff 
#check band_eq_true_eq_eq_tt_and_eq_tt

-/


#check band_eq_false_eq_eq_ff_or_eq_ff 
#check band_eq_true_eq_eq_tt_and_eq_tt

def sortedp : list ℕ → Prop -- note: returns Prop, not bool 
  | [] := true
  | [_] := true  
  | (x :: (y :: L)) := (leq x y = tt) ∧ (sortedp (y :: L)) 
-- 

def sortedb : list ℕ → bool 
  | [] := tt 
  | [_] := tt 
  | (x :: (y :: L)) := (leq x y) && (sortedb (y :: L)) 
--


-- choose one of the two theorems below to prove: 
#check insrt 
#check isort


theorem isort_sortedp:  ∀ L : list ℕ, sortedp (isort L)
:= begin
  intros,
  induction L with h L ih,
  {
    dunfold isort,
    dunfold sortedp,
    trivial,
  },
  {
    
    
  }
end

theorem isort_sortedb:  ∀ L : list ℕ, sortedb (isort L) = tt 
:= begin
  intros,
  induction L with h L ih,
  {
    dunfold isort,
    dunfold sortedb,
    refl,
  },
  {
    dunfold isort,

  }
end