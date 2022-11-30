-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 8

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Alyssa Mui, Justin Pong, Nelson Dong
-/



/-
Technical instructions: same as in the last homework plus ADDITIONAL INSTRUCTIONS:

you are NOT allowed to use functional induction in this homework. 
-/


/- IMPORTANT: 

for ALL problems in this and following homework sets, you should do two things: 

first, try to prove whatever it is you are proving _without_ induction. you don't always need induction. you often do, but not always. if you did use induction in your proof, go back and check: did you ever actually use the induction hypothesis? if you didn't, you don't need induction. go back and remove it from your proof (e.g., replace it by cases) and see whether you can complete the proof without induction. 

second, every time you use induction, try to MANUALLY GENERATE the following without LEAN's help:
1. BASE CASE(S)
2. INDUCTION STEP(S)
3. INDUCTION HYPOTHESI(E)S 

then you can check to see whether what you got is the same thing as what LEAN generates. if they are not the same, ask yourselves why. 

YOU WILL BE ASKED TO DO THIS TYPE OF MANUAL GENERATION IN EXAMS AND QUIZZES!
-/

import .ourlibrary11 
import .ourlibrary12 
import .ourlibrary14



/- HWK08-01: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem mult_1_x: ∀ x : ℕ, mult 1 x = x
-- ANSWER:
:= begin
  intros x,
  induction x with z ih, {
    dunfold mult,
    rw plus,
  },
  {
    dunfold mult,
    dunfold plus,
    rw succeq,
    dunfold mult at ih,
    exact ih,
  }
end

/- HWK08-02: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem mult_2_x: ∀ x : ℕ, mult 2 x = plus x x
-- ANSWER:
:= begin
  intros x,
  induction x with z ih, {
    dunfold mult,
    rw plus,
  },
  {
    dunfold mult,
    dunfold plus,
    dunfold mult at ih,
    rw succeq,
    cases z,
    {
      refl,
    },
    {
      dunfold plus,
      rw succeq,
      rw plus_x_zero,
    }
  }
end


/- HWK08-03: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem genzeros_n_len_n: ∀ n : ℕ, len (genzeros n) = n 
-- ANSWER:
:= begin 
  intros x,
  induction x with z ih, {
    rw genzeros,
    rw len,
  },
  {
    dunfold genzeros,
    dunfold len,
    rw succeq,
    exact ih,
  }
end
       

/- HWK08-04: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem map_identity: ∀ L : list ℕ, apply L (λ x, x) = L 
-- ANSWER:
:= begin
  intros L,
  induction L with n L ih, {
    rw apply,
  },
  {
    rw apply,
    rw listeq,
    rw ih,
    split, repeat {
      refl,
    }
  }
end 


/- HWK08-05: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem even_double: ∀ x : ℕ, even (double x) = tt 
-- ANSWER:
:= begin
  intros x,
  induction x with z ih, {
    rw double,
    rw even,
  },
  {
    dunfold double,
    rw even,
    exact ih,
  }
end



/- HWK08-06:
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem plus_assoc: 
    ∀ x y z : ℕ, plus x (plus y z) = plus (plus x y) z 
-- ANSWER:
:= begin
  intros x y z,
  induction x with y ih, {
    dunfold plus,
    refl,
  },
  {
    dunfold plus,
    rw succeq,
    exact ih,
  }
end




/- HWK08-07:
is the claim below true? if so prove it, if not, exhibit a counterexample:

theorem rev_app_distr: ∀ L1 L2 : list ℕ,
    rev (app L1 L2) = app (rev L2) (rev L1) 

-/
-- ANSWER: app (app (rev (y :: K)) (rev L)) [x]

theorem test : ∀ (x : ℕ) (L : list ℕ), (rev (x :: L)) = app (rev L) [x]
:= begin
  intros x L,
  induction L with y L ih,
  {
    refl,
  },
  {
    rw rev,
  }
end

theorem test2 : ∀ (x : ℕ) (L1 L2 : list ℕ), (app L1 (app (rev L2) [x])) = app (app L1 (rev L2)) [x]
:= begin
  intros x L1 L2,
  induction L1 with y L ih,
  {
    refl,
  },
  {
    rw app,
    rw app,
    rw ih,
    rw app,
  }
end

theorem rev_app_distr: ∀ L1 L2 : list ℕ,
    rev (app L1 L2) = app (rev L2) (rev L1) 
:= begin
  intros L1 L2,
  induction L1 with x L ih2, {
    dunfold rev,
    dunfold app,
    rw app_L_nil,
  },
  {
    dunfold app,
    rw rev,
    cases L2 with y K,
    {
      dunfold rev,
      rw ih2,
      refl,
    },
    {
      rw ih2,
      rw test,
      rw test,
      rw test2,
    }
  }
end 


/- HWK08-08:
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem test3 : ∀ (x : ℕ) (L : list ℕ), rev (app L [x]) = app [x] (rev L)
:= begin
  intros x L,
  induction L with y L ih,
  {
    refl,
  },
  {
    rw app,
    rw rev,
    rw ih,
    rw rev,
    dunfold app,
    refl,
  }
end

theorem rev_involutive : ∀ L : list nat, rev (rev L) = L 
-- ANSWER: rev (app (rev L) [x])
:= begin
  intros L,
  induction L with x L ih, {
    dunfold rev,
    refl,
  },
  {
    rw rev,
    rw test3,
    rw ih,
    dunfold app,
    refl,
  }
end



theorem rev_nil :  rev [] = [] :=
begin
  rw rev,
end

/- HWK08-09:
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem test4 : ∀ (x : ℕ) (L : list ℕ), x :: L = app [x] L
:= begin
  intros x L,
  dunfold app,
  refl,
end

theorem test6: ∀ 

theorem test5 : ∀ (x : ℕ) (L : list ℕ), app [x] L = rev (app (rev L) [x])
:= begin
  intros x L,
  induction L with y L2 ih,
  {
    refl,
  },
  {
    rw rev,
    rw <- rev,
    rw <- rev,
  }
end

theorem rev_left_right: ∀ L1 L2 : list nat, rev L1 = L2 → L1 = rev L2 
-- ANSWER: app [y] L3 = rev (app (rev L3) [y])
:= begin
  intros L1 L2,
  induction L1 with y L3 ih, {
    intros h,
    rw rev_nil at h,
    rw h,
    rw <- h,
    rw rev,
  },
  {
    intro h,
    rw test4,
    rw <- h,
    rw rev,
    rw <- rev,
    cases L3 with z L4,
    {
      dunfold rev,
      dunfold app,
      dunfold rev,
      dunfold app,
      refl,
    },
    {
      
    }
    
  }
end


theorem app_len_succ : ∀ (L : list nat) (x:ℕ), len (app L [x]) = (len L).succ
:= begin
  intros L x,
  induction L with x L ih, {
    rw app,
    rw len,
  },
  {
    dunfold len,
    dunfold app,
    dunfold len,
    rw succeq,
    exact ih,
  }
end 


/- HWK08-10:
is the claim below true? if so prove it, if not, exhibit a counterexample:

theorem rev_length: ∀ L : list ℕ, len (rev L) = len L 

-/
-- ANSWER: 

theorem rev_length: ∀ L : list ℕ, len (rev L) = len L 
:= begin
  intros L,
  induction L with x L2 ih, {
    rw rev,
  },
  {
    dunfold rev,
    dunfold len,
    rw app_len_succ,
    rw succeq,
    exact ih,
  }
end




/- HWK08-11:
is the claim below true? if so prove it, if not, exhibit a counterexample:

theorem mult_commut: ∀ x y : ℕ, mult x y = mult y x 

-/
-- ANSWER: 

theorem mult_0: ∀ x : ℕ , mult x 0 = 0
:= begin
  intros x,
  induction x with z ih, {
    rw mult,
  },
  {
    rw mult,
    rw plus,
    exact ih
  }
end

theorem mult_y_z: ∀ (y : ℕ) (z : ℕ) , plus y (mult y z) = mult y z.succ
:= begin
  intros y z,
  induction y with x ih, {
    dunfold plus,
    dunfold mult,
    refl
  },
  {
    dunfold plus,
    dunfold mult,
    dunfold plus,
    rw succeq,
    
  }
end

theorem mult_commut: ∀ x y : ℕ, mult x y = mult y x 
:= begin
  intros x y,
  induction x with z ih, {
    dunfold mult,
    rw mult_0,
  },
  {
    dunfold mult,
    rw ih,
    
  }
end



/- HWK08-12:
 prove app_assoc4:

HINT: There is a (really really) short proof for this one. If you find yourself getting tangled up, step back and try to look for a simpler way. 
-/
theorem app_assoc4: ∀ L1 L2 L3 L4 : list nat, 
    app L1 (app L2 (app L3 L4)) = app (app (app L1 L2) L3) L4 
:= begin
-- ANSWER:
    ... 
end






/- HWK08-13:
 prove that functions even and even_v2 are equivalent:

 theorem even_equiv_even_v2: ∀ x : ℕ, even x = even_v2 x 

-/
-- defined in library:
#check even 
#check even_v2 

-- ANSWER: 

theorem even_equiv_even_v2: ∀ x : ℕ, even x = even_v2 x 




/- HWK08-14:
prove that xor is associative. 

theorem xor_assoc: ∀ x y z : Prop, (xor x (xor y z)) ↔ (xor (xor x y) z) 

note: my proof uses many lemmas. 
-/
-- ANSWER:

theorem xor_assoc: ∀ x y z : Prop, (xor x (xor y z)) ↔ (xor (xor x y) z) 
... 



/- HWK08-15: 

in this problem we will formalize the so-called "drinker's paradox" which goes like this: "There is someone in the pub such that, if they are drinking milk, then everyone in the pub is drinking milk." write a LEAN theorem expressing this fact. do not prove the theorem, just state it. 

notes: 
  - you can represent people in the pub by nats, so that "everyone in the pub" can be written as ∀ x : ℕ 
  - use the existential quantifier ∃ (exists) for "there is someone" 
  - you can represent the fact that someone drinks milk as a predicate Milk : ℕ → Prop, so that (Milk x) holds if x drinks milk, otherwise (Milk x) does not hold
  - think about why this statement is true (it is!) and notice that the truth of the statement doesn't depend on what everyone is drinking: milk, water, vodka, or anything else! so in fact the statement holds for _any_ predicate Drinks : ℕ → Prop. use the higher-order capability of LEAN to quantify your claim over all possible such predicates. 

you don't have to prove the theorem. just state it. (for those of you who are curious and want to go further, the theorem can be proven using LEAN's exists.elim axiom and existsi tactic.) 
-/
-- ANSWER:
theorem drinker: ...   
:= begin
  sorry,
end




/- HWK08-16-1:
define the finite inductive type "binop" which represents the 5 binary logical connectives: "and", "or", "imp" (implies), "iff", "xor". use these 5 names for the constructors of "binop". 
-/

inductive binop : Type 
-- ANSWER:
  ... 
--

/- HWK08-16-2:
define the inductive type "bx" which represents all boolean expressions. bx will have 4 constructors, corresponding to the following 4 kinds of boolean expressions:
    1. if b is a bool, then (bxconst b) is a bx  (constant tt or ff) 
    2. if s is a string, then (bxvar s) is a bx  (variable)
    3. if e is a bx then (bxnot e) is a bx 
    4. if o is a binop, and e1 and e2 are both bx, then (bxbin o e1 e2) is a bx
-/
inductive bx : Type 
-- ANSWER:
  ... 
--

/- HWK08-16-3:
write each of the boolean expressions below as elements of the type bx:
-/
-- (x → y) → x 
-- ANSWER:
#check ... 

-- (p ∨ q) ∧ (p ∧ ¬r)
-- ANSWER:
#check ... 