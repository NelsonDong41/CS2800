-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 9

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: ...
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
... 
end


theorem eqb_refl: ∀ x : ℕ, eqb x x = tt 
:= begin
-- ANSWER:
... 
end

theorem leq_x_succ_x: ∀ x : ℕ, leq x (nat.succ x) = tt 
:= begin
-- ANSWER:
... 
end


theorem eqb_eq_zero: ∀ x : ℕ, eqb x 0 = tt → x = 0 
:= begin
-- ANSWER:
... 
end





/- HWK09-02: 
prove the following theorem:
-/
theorem eqb_iff_eq: ∀ x y : ℕ, eqb x y = tt ↔ x = y 
:= begin
  intros,
  split,
  {
    revert x,
    cases y,
    {
      intro x,
      intro h,
      cases x,
      {
        rw eqb at h,
      },
      {
        rw eqb at h,
        contradiction
      }
    },
    {
      intros x h,
      induction x with x ih,
      {
        dunfold eqb at h,
        trivial,
      },
      {
        dunfold eqb at h,
        induction y,
        {
          rw ih, {
            rw <- ih,
            {
              trivial,
            }
          }
        }
      }
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
lemma lemma4plus : ∀ y : ℕ, plus y 0 = plus 0 y :=
begin
  intro,
  induction y with y yih,
  {
    rw plus,
  },
  {
    dunfold plus,
    rw succeq,
    rw yih,
    refl,
  }
end

lemma lemma4mult : ∀ y : ℕ, mult y 0 = mult 0 y :=
begin
  intro,
  induction y with y yih,
  {
    rw mult,
  },
  {
    dunfold mult,
    rw yih,
    refl,
  }
end

theorem mult_assoc: 
   ∀ x y z : ℕ, mult x (mult y z) = mult (mult x y) z 
:= begin
  intros,
  induction x with x xih,
  {
    cases y,
    repeat {
      cases z,
      repeat {
        dunfold mult,
        refl,
      },
    }
  },
  {
    induction y with y yih,
    {
      dunfold mult,
      dunfold mult at xih,
      dunfold plus,
      assumption,
    },
    {
      induction z with z zih,
      {
        dunfold mult,
        dunfold mult at xih,
        dunfold plus,
        dunfold plus at xih,
        dunfold mult,
        dunfold plus,
        rw lemma4mult,
        dunfold mult,
        dunfold plus,
        rw lemma4mult,
        dunfold mult,
        rw lemma4mult,
        dunfold mult,
        rw lemma4mult at yih,
      },
      {
        dunfold mult,
        dunfold plus,
        dunfold mult at zih,
        dunfold plus at zih,
        dunfold mult at zih,
        dunfold mult at yih,
        dunfold mult at xih,

      }
    }
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
  intros,

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
  
end 


/- HWK09-06-2:

prove the following:

theorem plus4_zero_x: ∀ x : ℕ, plus4 0 x = x 

hint: use lemma discovery by generalization. 
-/
-- ANSWER:


lemma lemm4: ∀ x, plus4 1 x = (plus 0 x).succ :=
begin
  intros,
  rw
end

theorem plus4_zero_x: ∀ x : ℕ, plus4 0 x = x 
:= begin
  intros,
  cases x,
  {
    dunfold plus4,
    refl
  },
  {
    dunfold plus4,

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



lemma lemma7 : ∀ x y : nat, plus1 x y.succ = (plus1 x y).succ :=
begin
  intros x y,
  revert x,
  induction y,
  {
    intros,
    have h1 :∀ x y : nat, plus1 x y = plus1 y x := begin
      cases x,
      {
        
        
      },
      {
        dunfold plus1,
        
      }
    end,
    refl
  },
  {
    revert x_n,
    intros,
    
  }
end



theorem plus1_equiv_plus: ∀ x y : nat, plus1 x y = plus x y 
:= begin
  intros,
  induction x with x ih,
  {
    dunfold plus,
    dunfold plus1,
    refl,
  },
  {
    rw plus1,
    rw plus,
    rw <- ih,
    cases y,
    {
      rw ih,
      cases x,
      {
        refl,
      },
      {
        rw <- ih,
        rw plus1,
      }
    }
  }
end

theorem plus_equiv_plus3: ∀ x y : nat, plus x y = plus3 x y
:= begin
  intros,
  induction x,
  {
    rw plus,
    induction y,
    {
      rw plus3,
    },
    {
      rw plus3,
      rw succeq,
      assumption
    }
  },
  {
    rw plus,
    induction y,
    {
      rw plus3,
      rw succeq,
      rw x_ih,
      rw plus3,
    },
    {
      rw x_ih,
      dunfold plus3,
      rw succeq,
      rw <- y_ih,
      {
        rw succeq,
        
      }
    }
  }
end

theorem plus3_equiv_plus4: ∀ x y : nat, plus3 x y = plus4 x y
:= begin
...
end







/- HWK09-08: 
prove the following:
-/
theorem plus_n_n_injective: ∀ n m : ℕ, (plus n n = plus m m) → n = m 
:= begin
-- ANSWER:
  intros n m h,
  induction n with n nih,
  {
    cases m,
    {
      rw plus at h,
    },
    {
      dunfold plus at h,
      contradiction
    }
  },
  {
    induction m with m mih,
    {
      dunfold plus at h,
      contradiction
    },
    {
      dunfold plus at h,
      rw succeq,
      rw succeq at h,

    }
  }
end




/- HWK09-09:
Prove the theorem rev_nil_implies_nil:
-/
-- ANSWER: 
theorem lemma9 : ∀ (L : list ℕ) (x : ℕ ), app (rev L) [x] = [] -> false
:= begin
  intros L x h,
  induction L with y L ih,
  {
    dunfold rev at h,
    dunfold app at h,
    contradiction
  },
  {
    
  }
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

lemma leq_lem : ∀ ( x y : ℕ ), ¬leq x y = tt → leq y x = tt:=
begin
  intros x,
  induction x with x ih,
  {
    intros y h,
    rw leq at h,
    contradiction,
  },
  {
    intros y h,
    cases y, {
      rw leq at h,
      trivial,
    },
    {
      rw leq at h,
      rw leq,
      rw ih,
      exact h,
    }
  }

end


lemma lem : ∀ ( x : ℕ ),  ff = leq x 0 <-> leq x 0 = ff :=
begin
  intros,
  split,
  {
    intro h,
    rw h,
  },
  {
    intro h,
    rw <- h,
  }
end


theorem isort_sortedp:  ∀ L : list ℕ, sortedp (isort L)
:= begin
  intros,
  induction L with x xL xih,
  {
    dunfold isort,
    dunfold sortedp,
    trivial,
  },
  {
    rw isort,
    cases (isort xL) with y yL yih, 
    trivial,
    {
      dunfold insrt,
      have h1 := classical.em (leq x y = tt),
      cases h1,
      {
        rw itetrue,
        {
          dunfold sortedp,
          split,
          repeat{
            assumption
          }
        },
        assumption
      },
      {
        rw itefalse,
        {
          revert y,
          induction (insrt x yL),
          {
            intros,
            dunfold sortedp,
            trivial
          },
          {
            intros,
            have h2 := ih y xih h1,
            
          }
          -- revert x y,
          -- induction yL with yLx yL yih,
          -- {
          --   dunfold insrt,
          --   dunfold sortedp,
          --   intros,
          --   split,
          --   {
          --     induction x,
          --     {
          --       intros,
          --       rw leq_lem,
          --       assumption,
          --     },
          --     {
          --       intros,
          --       rw leq_lem,
          --       assumption,
          --     }
          --   },
          --   {
          --     assumption,
          --   }
          -- },
          -- {
          --   intros,
          --   have h2 : sortedp (y :: insrt x (yLx :: yL)) -> sortedp (y :: insrt x yL):=
          --   begin
          --     intros h2,

          --   end,
          -- }
        },
        {
          assumption
        }
      }
    }
  }
end