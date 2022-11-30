-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary16 
import .leq_properties -- this file won't be posted on canvas, comment it out and complete any missing lemma proofs 



/-
TRACE evaluations are now open: you should have received notifications from the university. 

please take the surveys: they are anonymous and confidential!

the surveys will close on on Fri 16 Dec. 
-/




-- QUIZ TIME! 





/-
  homework 10 review 
-/




---------------------------------------------
-- MEASURE FUNCTIONS AND PROOFS PRACTICE !
---------------------------------------------

-- MAKE SURE YOU ARE ABLE TO PROVE ALL THESE! 
#check ltb_succ -- ltb_succ : ∀ (x : ℕ), ltb x (nat.succ x) = tt
lemma ltb_succ : ∀ (x : ℕ), ltb x (nat.succ x) = tt := begin
  intros,
  induction x with x ih,
  {
    dunfold ltb,
    refl,
  },
  {
    rw ltb,
    assumption
  }
end
#check ltb_succ_succ -- ltb_succ_succ : ∀ (x : ℕ), ltb x (nat.succ (nat.succ x)) = tt
lemma ltb_succ_succ : ∀ (x : ℕ), ltb x (nat.succ (nat.succ x)) = tt := begin
  intros,
  induction x with x ih,
  {
    rw ltb,
  },
  {
    dunfold ltb,
    assumption
  }
end
#check ltb_trans -- ltb_trans : ∀ (x y z : ℕ), ltb x y = tt → ltb y z = tt → ltb x z = tt
lemma ltb_trans : ∀ (x y z : ℕ), ltb x y = tt → ltb y z = tt → ltb x z = tt := begin
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
        dunfold ltb at h1,
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
        dunfold ltb at h1,
        have h2 := ih y z h h1,
        assumption
      }
    }
  }
end
#check ltb_plus_right --ltb_plus_right : ∀ (x y z : ℕ), ltb x y = tt → ltb (plus x z) (plus y z) = tt
lemma ltb_plus_right : ∀ (x y z : ℕ), ltb x y = tt → ltb (plus x z) (plus y z) = tt := begin
  intros x y z h,
  revert x y,
  induction z with z ih,
  {
    intros,
    rw plus_x_zero,
    rw plus_x_zero,
    assumption
  },
  {
    intros,
    have h1 := ih x y h,
    have h2 : ∀a b:ℕ , plus a b.succ = (plus a b).succ :=
    begin
      intros,
      revert b,
      induction a with a ih,
      {
        intros,
        dunfold plus,
        refl
      },
      {
        intros,
        dunfold plus,
        rw succeq,
        rw ih, 
      }
    end,
    rw h2,
    rw h2,
    dunfold ltb,
    rw ih,
    assumption
  }
end

#check x_ltb_y_plus_z -- x_ltb_y_plus_z : ∀ (x y z : ℕ), ltb x y = tt → ltb x (plus y z) = tt
theorem x_ltb_y_plus_z : ∀ (x y z : ℕ), ltb x y = tt → ltb x (plus y z) = tt := begin
  intros x y z h,
  revert y z,
  induction x with x ih,
  {
    intros,
    cases y,
    {
      dunfold plus,
      dunfold ltb at h,
      contradiction
    },
    {
      dunfold ltb at h,
      trivial,
    }
  },
  {
    intros,
    cases y,
    {
      dunfold plus,
      rw ltb at h,
      contradiction
    },
    {
      dunfold ltb at h,
      dunfold plus,
      dunfold ltb,
      rw ih,
      assumption
    }
  }
end


/-
proofs for ltb_plus_right and x_ltb_y_plus_z are provided below. make sure you try them first on your own, before you look at the solutions! 
-/



section local_notation
local notation (name := plus) x + y := plus x y 
local notation (name := minus) x - y := minus x y 
local notation (name := mult) x * y := mult x y 
local notation (name := leq) x ≤ y := leq x y = tt  
local notation (name := ltb) x < y := ltb x y = tt  


/- PRACTICE: for each function given below:

1. devise a measure function

2. generate the decreasing measure proof obligation(s) 

3. prove the decreasing measure proof obligation(s) 

FIRST DO IT ON YOUR OWN, THEN SCROLL DOWN TO SEE THE ANSWERS. 
-/


-------------------------------------------------------
#check eqb 
/- 
def eqb : ℕ → ℕ → bool 
    | 0 0 := tt 
    | 0 (nat.succ y) := ff     
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := eqb x y 
-/

def m_eqb : ℕ → ℕ →  ℕ := fun x y, x + y

theorem m_eqb_decreases : ∀ x y, m_eqb x y < m_eqb (x.succ) (y.succ) :=
begin
  intros,
  cases x,
  {
    dunfold m_eqb,
    dunfold plus,
    cases y with y ih,
    {
      refl,
    },
    {
      have h1 :=  ltb_succ_succ y.succ,
      assumption
    }
  },
  {
    have h1 : ∀ x y : ℕ , x < y -> x.succ < y.succ := begin
      intros a b h,
      cases a,
      {
        cases b,
        {
          trivial,
        },
        {
          trivial,
        }
      },
      {
        cases b,
        {
          contradiction
        },
        {
          assumption
        }
      }
    end, 
    cases y,
    {
      dunfold m_eqb,
      dunfold plus,
      rw <- h1,
      rw plus_x_zero,
      have h2 : plus x 1 = x.succ := begin
        induction x with x ih,
        {
          refl,
        },
        {
          dunfold plus,
          rw succeq,
          assumption,
        }
      end,
      rw h2,
      rw ltb_succ_succ,
    },
    {
      dunfold m_eqb,
      dunfold plus,
      rw ltb,
      have h2 : ∀ a b : ℕ , a + b.succ = (a + b).succ :=
      begin
        intros,
        induction a with a ih,
        {
          cases b,
          {
            trivial,
          },
          {
            trivial,
          }
        },
        {
          dunfold plus,
          rw succeq,
          assumption
        }
      end,
      rw h2,
      rw h2,
      rw h1,
      rw h2,
      rw ltb_succ_succ,
    }
  }
end



------------------------------------------------

def ind4 : ℕ → ℕ 
  | 0 := 2*3   
  | (nat.succ x) := 2*(ind4 x) + (ind4 (x-1))  

def m_ind4 : ℕ -> ℕ := fun x, x

def m_ind4_decreasing : ∀ x:nat,  m_ind4 x < m_ind4 (nat.succ x) := 
begin
  intros,
  dunfold m_ind4,
  induction x with x ih,
  {
    trivial
  },
  {
    assumption,
  }
end


------------------------------------------------

def app_t2 : list ℕ → list ℕ → list ℕ → list ℕ 
  | [] [] acc := acc
  | [] (b :: L) acc := app_t2 [] L (b :: acc)
  | (a :: L1) L2 acc := app_t2 L1 L2 (a :: acc)

def m_app_t2 : list ℕ -> list ℕ → list ℕ → ℕ
  | x y z := len x + len y

def m_app_t2_dec_one : ∀ (y z : list ℕ) (a: ℕ ),  m_app_t2 [] y (a :: z) < m_app_t2 [] (a :: y) z:=
begin
  intros,
  dunfold m_app_t2,
  dunfold len,
  dunfold plus,
  rw ltb_succ,
end

def m_app_t2_dec_two : ∀ (x y z :list ℕ ) (a : ℕ ), m_app_t2 x y (a :: z) < m_app_t2 (a :: x) y z :=
begin
  intros,
  dunfold m_app_t2,
  dunfold len,
  dunfold plus,
  rw ltb_succ,
end

/-
ANSWERS:
-/

------------------------------------------------
#check eqb 
/- 
def eqb : ℕ → ℕ → bool 
    | 0 0 := tt 
    | 0 (nat.succ y) := ff     
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := eqb x y 
-/

-- ANSWER: 
/-
there's actually many measure functions we can use:
-/

def m1_eqb : ℕ → ℕ → ℕ := λ x y, x 
def m2_eqb : ℕ → ℕ → ℕ := λ x y, y 
def m3_eqb : ℕ → ℕ → ℕ := λ x y, x + 1 
def m4_eqb : ℕ → ℕ → ℕ := fun x y, x + y 
-- etc ...  

/-
To show that m1_eqb is a valid measure function for eqb we have to show that it decreases on every recursive call of eqb, under the conditions that led to that call.

eqb has just one recursive call, so we have to show:
-/

theorem m1_eqb_decreases: forall x y : ℕ,
  m1_eqb x y < m1_eqb (nat.succ x) (nat.succ y) 
:= begin
  intros,
  induction x with z ih,
  {
    refl,
  },
  {
    dunfold m1_eqb,
    dunfold ltb,
    rw ltb_succ,
  }
end

-- similarly for m2_eqb:
theorem m2_eqb_decreases: forall x y : ℕ,
  m2_eqb x y < m2_eqb (nat.succ x) (nat.succ y) 
:= begin
  intros,
  induction y with z ih,
  {
    refl,
  },
  {
    dunfold m2_eqb,
    dunfold ltb,
    rw ltb_succ,
  }
end

-- similarly for m3_eqb:
theorem m3_eqb_decreases: forall x y : ℕ,
  m3_eqb x y < m3_eqb (nat.succ x) (nat.succ y) 
:= begin
  intros,
  induction x with z ih,
  {
    refl,
  },
  {
    dunfold m3_eqb,
    dunfold plus,
    dunfold ltb,
    rw ltb_succ,
  }
end

-- similarly for m4_eqb:
theorem m4_eqb_decreases: forall x y : ℕ,
  m4_eqb x y < m4_eqb (nat.succ x) (nat.succ y) 
:= begin
  intros,
  induction x with z ih,
  {
    dunfold m4_eqb,
    dunfold plus,
    have h1 := ltb_succ y,
    have h2 := ltb_succ (nat.succ y),
    have h3 := ltb_trans y (nat.succ y) (nat.succ (nat.succ y)) h1 h2, 
    assumption,
  },
  {
    dunfold m4_eqb,
    dunfold plus,
    dunfold ltb,
    rw <- plus_x_succ_y,
    have h1 := ltb_succ (z + y),
    have h2 := ltb_succ (nat.succ (z+y)),
    have h3 := ltb_trans (z+y) (nat.succ (z+y)) (nat.succ (nat.succ (z+y))) h1 h2,
    assumption,
  }
end




------------------------------------------------
/-
def ind4 : ℕ → ℕ 
  | 0 := 2*3   
  | (nat.succ x) := 2*(ind4 x) + (ind4 (x-1))  
-/

def m_ind4 : ℕ → ℕ := id 

theorem m_ind4_decreases1: ∀ x : ℕ, x < nat.succ x := ltb_succ 

lemma x_minus_0: ∀ x : ℕ, x - 0 = x 
:= begin
  intro,
  cases x with y,
  refl,
  refl,
end

theorem m_ind4_decreases2: ∀ x : ℕ, x-1 < nat.succ x 
:= begin
  intro,
  cases x with y,
  {
    refl,
  },
  {
    dunfold minus,
    rw x_minus_0,
    rw ltb_succ_succ,
  }
end




------------------------------------------------
/-
def app_t2 : list ℕ → list ℕ → list ℕ → list ℕ 
  | [] [] acc := acc
  | [] (b :: L) acc := app_t2 [] L (b :: acc)
  | (a :: L1) L2 acc := app_t2 L1 L2 (a :: acc)
-/
/- for "weird-looking" functions like this one and the ones below, it might be a good idea to execute them first, in order to gain some intuition as to how exactly they work. a good way to do this is by using _example_ and _rw_ to do step-by-step unfolding of the function definition:
-/

example: app_t2 [1,2,3] [5,6,7] [10,11,12] = [] /- we don't yet know what the result would be, but it doesn't matter. our goal is not to prove a valid equality, our goal is to simulate/debug the execution of the function step by step! -/
:= begin
  rw app_t2,
  rw app_t2,
  rw app_t2,
  rw app_t2,
  rw app_t2,
  rw app_t2,
  rw app_t2, -- done! we also found out that the result is [7, 6, 5, 3, 2, 1, 10, 11, 12] 
  sorry,
end

-- from the above step-by-step execution we found out the output. we can state this now as a test:
example: app_t2 [1,2,3] [5,6,7] [10,11,12] = [7, 6, 5, 3, 2, 1, 10, 11, 12] 
:= begin refl, end 


/- ungraded quiz: what is a measure function for app_t2?
-/
def m_app_t2 : list ℕ → list ℕ → list ℕ → ℕ := fun L1 L2 L3, (len L1) + (len L2) 


/- ungraded quiz: what are the decreasing measure proof obligations for m_app_t2?
-/
-- there are two recursive calls, so we have 2 decreasing measure proof obligations:
theorem m_app_t2_decreases_call1: ∀ (L acc : list ℕ) (b : ℕ),
  m_app_t2 [] L (b :: acc) < m_app_t2 [] (b :: L) acc 
:= begin
 intros,
 dunfold m_app_t2,
 dunfold len,
 dunfold plus,
 rw ltb_succ,
end

theorem m_app_t2_decreases_call2: ∀ (L1 L2 acc : list ℕ) (a : ℕ),
  m_app_t2 L1 L2 (a :: acc) < m_app_t2 (a :: L1) L2 acc 
:= begin
  intros,
  dunfold m_app_t2,
  dunfold len,
  dunfold plus,
  rw ltb_succ,
end




end local_notation 




lemma l1: ∀ z u : ℕ, ltb z (nat.succ (plus u z)) = tt
:= begin
  intros,
  induction z with x ih,
  {
    refl,
  },
  {
    rw ltb,
    rw <- plus_x_succ_y,
    exact ih,
  },
end

lemma ltb_plus_right_proof1 : 
  ∀ (x y z : ℕ), ltb x y = tt → ltb (plus x z) (plus y z) = tt
:= begin
  intro,
  induction x with w ih,
  {
    intro,
    intro,
    intro h,
    rw plus,
    cases y with u,
    {
      rw ltb at h,
      trivial,
    },
    {
      rw plus,
      rw l1,
    }
  },
  {
    intro,
    intro,
    intro h,
    rw plus,
    cases y with u,
    {
      rw ltb at h,
      trivial,
    },
    {
      rw ltb at h,
      rw plus,
      rw ltb,
      have h2 := ih u z h ,
      exact h2,
    }
  },
end

lemma ltb_plus_right_proof2 : 
  ∀ (x y z : ℕ), ltb x y = tt → ltb (plus x z) (plus y z) = tt
:= begin
  intros x y z h1,
  induction z with w ih,
  {
    rw plus_x_zero,
    rw plus_x_zero,
    assumption,
  },
  {
    rw plus_commut,
    rw plus_commut y,
    dunfold plus,
    rw ltb,
    rw plus_commut,
    rw plus_commut w,
    assumption,
  }
end

lemma x_ltb_y_plus_z_proof : 
  ∀ (x y z : ℕ), ltb x y = tt → ltb x (plus y z) = tt
:= begin
  intro,
  induction x with w ih,
  {
    intro,
    intro,
    intro h,
    cases y with u,
    {
      rw ltb at h,
      trivial,
    },
    {
      rw plus,
      rw ltb,
    },
  },
  {
    intro,
    intro,
    intro h,
    cases y with u,
    {
      rw ltb at h,
      trivial,
    },
    {
      rw plus,
      rw ltb,
      rw ltb at h,
      have h2 := ih u z h ,
      exact h2,
    }
  },
end

