-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 4

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Nelson Dong, Alyssa Mui, Justin Pong
-/

/-
Technical instructions: same as in the last homework. 
-/





/- HWK04-01:
Write as LEAN theorems the (1) commutativity and (2) associativity properties for the function mult given below (see in the lectures what commutativity and associativity means for plus, and adapt accordingly). Also write as LEAN theorems the following properties: (3) "0 times something is 0", (4) "1 times x is x", (5) "2 times x is x+x" (use our "plus" function for x+x). 

Start proving all these theorems and advance as much as you can given the tactics that we know. If you cannot finish your proof, end it with "sorry". note: it is expected that you will be able to finish at least one of these proofs.   
-/

def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
--

def mult : ℕ → ℕ → ℕ 
  | nat.zero _ := nat.zero 
  | (nat.succ x) y := plus y (mult x y)  
--

-- ANSWER:
theorem mult_commutative: ∀ x y : ℕ, mult x y = mult y x
:= begin
    intro,
    intro,
    cases x,
    {
      rw mult,
      cases y, 
      {
        refl,
      },
      {
        cases y,
        {
          refl,
        },
        sorry,
      }
    },
    sorry,
end

theorem mult_associative: ∀ x y z: ℕ, mult ( mult x y) z = mult x (mult y z)  
:= begin
    intros,
    cases x, {
      rw mult,
      rw mult,
      rw mult,
    },
    {
      rw mult,
      rw mult,
      sorry,
    }
end

theorem mult_0_x: ∀ x : ℕ , mult 0 x = 0
:= begin
  intros,
  rw mult
end

theorem mult_1_x: ∀ x : ℕ , mult 1 (nat.succ x) = (nat.succ x)
:= begin
   intros,
   rw mult,
   rw mult,
   rw plus,
   cases x,
   {
    rw plus,
   },
   {
    rw plus,
    cases x,
      {
        rw plus,
      },
      {
        rw plus,
        sorry,
      }
   }
end

theorem mult_2_x:  ∀ x : ℕ, mult 2 x = 2 * x 
:= begin
  intros,
  rw mult,
  cases x, {
    refl
  },
  cases x, {
    rw plus,
    rw mult,
    refl
  },
  sorry
end


/- HWK04-02:
plus and mult are our own functions, which are supposed to correspond to the predefined LEAN operators + and *. Write as two LEAN theorems the specification that plus must be equivalent to +, and that mult must be equivalent to *. Equivalent means that given the same inputs, they produce the same outputs. Start proving your theorems and advance as much as you can given the tactics that we know. End your proofs with "sorry". 
-/
-- ANSWER:
theorem plus_equiv: ∀ x y : ℕ,  (nat.succ x) + y = plus (nat.succ x) y  
:= begin
    intros,
    cases x,
    {
      rw plus,
      rw plus,
      cases y, 
      {
        refl
      },
       {
        sorry,
       },
    },
    {
      rw plus,
      rw plus,
      sorry,
    }
end

theorem mult_equiv: ∀ x y: ℕ , x * y = mult x y 
:= begin
    intros,
    cases x,
    {
      rw mult,
      cases y, 
      {
        refl,
      },
      {
        sorry,
      }
    },
    {
      sorry,
    }
end



/- HWK04-03:
Recall the "app" (append) function requested in HWK02, which concatenates two lists. A correct implementation of app is given below. Is app associative? If it is, write as a LEAN theorem the associativity property of app. Start proving the theorem and advance as much as you can given the tactics that we know. End your proof with "sorry". If you think that app is not associative, provide a counter-example (that is, three concrete lists L1, L2, L3, for which the associativity of app doesn't hold). 
-/

def app : list ℕ → list ℕ → list ℕ 
  | [] L := L 
  | (x :: L1) L2 := x :: (app L1 L2)
--

example: app [1,2,3] (app [4,5,6] [7,8]) = [1,2,3,4,5,6,7,8] 
:= begin refl, end 


-- ANSWER:

... 





/- HWK04-04:
recall the function genzeros requested in HWK02. a correct implementation of genzeros is provided below. write a theorem stating that the length of the list produced by the call (genzeros n) should be n, for any n. Start proving the theorem and advance as much as you can given the tactics that we know. End your proof with "sorry". 
note: you will need to redefine the function len (length of a list of nats) in order to use it in your theorem. 
-/

def len : list nat -> nat 
  | [] := 0 
  | (_ :: L) := nat.succ (len L)
--

def genzeros : ℕ → list ℕ 
  | 0 := []
  | (n+1) := 0 :: (genzeros n)
--

-- ANSWER:
theorem genzeros_n_len_n: ... 
:= begin
    ... 
end




/- HWK04-05:
consider the functions exponent and myexp given below. write a LEAN theorem stating that the two functions are "almost" equivalent, meaning that they are equivalent except when both inputs are 0. Start proving the theorem and advance as much as you can given the tactics that we know. End your proof with "sorry". 
-/

def exponent : ℕ → ℕ → ℕ 
  | _ 0 := 1
  | x (nat.succ n) := mult x (exponent x n)
--

def myexp : ℕ → ℕ → ℕ 
  | 0 _ := 0
  | (nat.succ x) 0 := 1
  | x (nat.succ n) := mult x (myexp x n) 
--

-- ANSWER:
theorem myexp_almost_equiv_to_exponent: 
   ... 
:= begin
  ... 
end





/- HWK04-06:
a correct implementation of the function list_delete requested in HWK03 is given below. write LEAN theorems stating the following properties of list_delete:
(1) "deleting from an empty list results in an empty list"
(2) "if i is out of bounds, then the output list should be the same as the input list"
(3) "provided i is within bounds, the length of the input list should be one plus the length of the output list". 

for this problem, to express "out of bounds" and "within bounds", you can use the <, ≤, ≥, > comparison operators on nats, see below. 

Start proving all these theorems and advance as much as you can given the tactics that we know. If you cannot finish your proof, end it with "sorry". note: it is expected that you will _not_ be able to finish all these proofs, but that you _will_ be able to finish some (at least one)!  
-/

def list_delete : list ℕ → ℕ → list ℕ 
  | [] _ := []
  | (x :: L) 0 := L 
  | (x :: L) (nat.succ i) := x :: (list_delete L i)

-- ANSWER:
theorem list_delete_empty: 
  ... 
:= begin
  ... 
end

theorem list_delete_outofbounds: 
  ... 
:= begin
  ... 
end

theorem list_delete_withinbounds:
  ... 
:= begin
  ... 
end





/- HWK04-07:
LEAN has predefined logical operators on booleans: &&, ||, and bnot, see below. state as LEAN theorems, and prove, all properties below:

(1) && is commutative and associative
(2) || is commutative and associative
(3) de Morgan's laws: 
  bnot(x && y) = (bnot x) || (bnot y)
  bnot(x || y) = (bnot x) && (bnot y)
(4) && distributes over || 
  x && (y || z) = (x && y) || (x && z)
(5) || distributes over && 
  x || (y && z) = (x || y) && (x || z)
-/

-- LEAN's boolean and:
#check tt && ff 
#reduce tt && ff 

-- LEAN's boolean or:
#check tt || ff 
#reduce tt || ff 

-- LEAN's boolean not:
#check bnot 
#reduce bnot ff 

-- ANSWERS:
theorem band_commut: ... 
:= begin
  ...
end 

theorem band_assoc: ... 
:= begin
  ...
end 

theorem bor_commut: ... 
:= begin
  ...
end 

theorem bor_assoc: ... 
:= begin
  ...
end 

theorem bool_deMorgan1: ... 
:= begin
  ...
end 

theorem bool_deMorgan2: ... 
:= begin
  ...
end 

theorem bool_and_distr_or: ... 
:= begin
  ...
end 

theorem bool_or_distr_and: ... 
:= begin
  ...
end 


/- HWK04-08:
prove that all three functions below, f, fg1, and fg2, are equivalent:
-/

def f (x : nat) (b : bool) := if (b = tt) then (x:int) else -x 

def fg1 : ℕ → bool → ℤ 
  | x b := if (b = tt) then (x:int) else -x 

def fg2 : ℕ → bool → ℤ 
  | x tt := (x:int)
  | x ff := -x 

-- ANSWER:
theorem f_equiv_fg1: ∀ (x : ℕ) (b : bool) , f x b = fg1 x b  
:= begin
  intros,
  rw f,
  rw fg1,
end 

theorem f_equiv_fg2: ∀ (x : ℕ ) (b : bool) , f x b = fg2 x b 
:= begin
  intros,
  rw f,
  cases x,
  {
    cases b,
    {
      refl,
    },
    {
      refl,
    }
  },
  {
    cases b,
    {
      refl,
    },
    {
      refl,
    }
  }
end 



/- HWK04-09:
here's two functions f1 and f2. your friend claims that the two functions are equivalent. prove your friend either correct, or wrong. to prove your friend correct, you have to state and prove the equivalence of these functions as a LEAN theorem. to prove them wrong, you have to exhibit a counter-example: you should exhibit the latter as a LEAN "example" that you also need to prove (with refl, as usual). 
-/

def f1 : bool → bool → bool → bool 
    | tt tt tt := tt
    | tt tt ff := ff 
    | tt ff tt := tt 
    | tt ff ff := ff
    | ff tt tt := ff
    | ff tt ff := tt
    | ff ff tt := tt
    | ff ff ff := ff 
--

def f2 : bool → bool → bool → bool 
    | ff ff tt := tt
    | tt ff tt := tt 
    | ff ff ff := ff 
    | tt tt tt := tt
    | tt ff ff := tt
    | ff tt ff := ff
    | tt tt ff := ff 
    | ff tt tt := ff
--

-- ANSWER:
theorem f1_equals_f2: 
∀ x y z : bool, f1 x y z = f2 x y z
:= begin
  intros,
  cases x,
  {
    cases y,
    {
      cases z,
      {
        refl,
      },
      {
        refl,
      },
    },
    {
      cases z,
      {
        rw f1,
        rw f2,
        sorry, --WRONG
      },
      sorry,
    }
  },
  sorry
 end

example : ¬ (f1 tt ff ff) = (f2 tt ff ff) := begin dunfold f1, dunfold f2, end




/- HWK04-10:
recall the function lenmul4 from HWK03, a correct implementation of which is provided below. state as a LEAN theorem the property that "for any list of exactly 4 nats, lenmul4 returns tt". Can you prove the theorem completely using the tactics that we know? If yes, finish the proof. If not, end your proof with "sorry". 
-/
def lenmul4 : list ℕ → bool 
    | [] := tt
    | [ _ ] := ff 
    | [_, _] := ff
    | [_, _, _] := ff 
    | (x :: y :: z :: w :: L) := lenmul4 L  
--

-- ANSWER:

theorem lenmul4_on_list_of_4: ... 
:= begin
  ...
end 




/- HWK04-11:
recall the function rl from HWK03. state as a LEAN theorem the property that "for any list of nats L, if we pass to rl L and the length of L, then rl will return the same list L". Can you prove the theorem completely using the tactics that we know? If yes, finish the proof. If not, end your proof with "sorry". 
-/


def rl : list ℕ → ℕ → list ℕ 
 | [] _ := []
 | (x :: L) 0 := (x :: L)
 | (x :: L) (n+1) := rl (L ++ [x]) n 
--

-- ANSWER:
theorem rl_L_len_L: ... 
:= begin
  ...
end 





/- HWK04-12:
recall the function apply from HWK03. find a function f such that the following property is true: "for any list of nats L, if we pass to apply L and f, then apply will return the same list L". Then state this property as a LEAN theorem. Start proving the theorem using the tactics that we know. Perform proof by cases on the list L, and prove the case where L is empty. You don't have to prove the other case. End your proof with "sorry". 
-/

def apply : list ℕ → (ℕ → ℕ) → list ℕ 
    | [] _ := []
    | (x :: L) f := (f x) :: (apply L f)
--

-- ANSWER:

theorem ... 
:= begin
  ...
end 



/- HWK04-13:
recall the functions curry, addpair, and add2 from HWK03. implementations for those can be found below. state as a LEAN theorem the property that "the curried version of addpair is equivalent to add2". Can you prove the theorem completely using the tactics that we know? If yes, finish the proof. If not, end your proof with "sorry". 
-/

def curry (f : ℕ × ℕ → ℕ) : (ℕ → ℕ → ℕ) := λ x y : nat, f(x,y) 

def addpair : ℕ × ℕ → ℕ
  | (x,y) := x + y

def add2 : ℕ → ℕ → ℕ 
  | x y := x + y 

-- ANSWER:
theorem addpair_equiv_add2: ∀ x y : ℕ , curry (addpair) x y = add2 x y 
:= begin
  intros,
  dunfold curry,
  dunfold addpair,
  dunfold add2,
  refl,
end 



/- HWK04-14:
suppose we have written a function F : (list nat) -> (list nat). formalize the claim "every list produced by F contains at least one element which is 0". write this claim as a forall-specification in LEAN. complete the LEAN theorem given below, but don't prove it. 

NOTE: you should NOT use ∃ (exists) quantifiers in your theorem. instead, you can define a helper function which captures for a given list L the property "L contains at least one element which is 0". then you can use this helper function in your forall-specification. 
-/

-- we suppose f exists, we don't care how it's defined 
constant F : (list nat) -> (list nat) 

def hasOneZero : list ℕ -> bool
  | [] := ff
  | [x] := x = 0
  | (x :: L) := x = 0 ∨ hasOneZero L

-- ANSWER:
example: ∀ x : list ℕ, hasOneZero ( F x) := begin sorry end





/- HWK04-15:
consider the inductive data type below:
-/

inductive foo : Type 
  | bar : foo 
  | ber : ℕ → foo → foo 
  | bor : foo → bool → foo → foo 

/- HWK04-15-1:
is foo a finite or is it an infinite type? why?
-/
-- ANSWER:
-- Yes it is infinite because all types of foo return a type foo, so as long as you use
-- another type of foo, it will be infinite

/- HWK04-15-2:
provide at least 3 distinct elements of foo, using ALL its constructors:
-/
-- ANSWER:
#check foo.bar 
#check foo.ber 2 foo.bar 
#check foo.bor foo.bar ff foo.bar 



/- HWK04-16-1: 
let's start formalizing the correctness of sorting programs like isort from your hwk01. define a function leq : ℕ → ℕ → bool, such that leq x y = tt iff x is less or equal to y. do NOT use LEAN's ≤ or similar operators to define leq. instead, define it from scratch, recursively, using pattern matching. make sure your function passes all tests provided below.  
-/
-- ANSWER:
def leq : ℕ → ℕ → bool 
  | 0 (nat.succ y) := tt
  | 0 0 := tt
  | (nat.succ x) 0 := ff
  | (nat.succ x) (nat.succ y) := leq x y


-- DO NOT DELETE:
example: leq 0 0 = tt := begin refl, end 
example: leq 0 1 = tt := begin refl, end 
example: leq 0 2 = tt := begin refl, end 
example: leq 1 0 = ff := begin refl, end 
example: leq 1 1 = tt := begin refl, end 
example: leq 1 2 = tt := begin refl, end 
example: leq 10 0 = ff := begin refl, end 
example: leq 10 1 = ff := begin refl, end 
example: leq 10 2 = ff := begin refl, end 


/- HWK04-16-2: 
define a function sorted : list ℕ → bool, such that sorted L = tt iff L is sorted in increasing order. again, define sorted from scratch. you can use the leq function you defined above. you can also use operators on bools: &&, ||, bnot, etc. make sure your function passes all tests below.  
-/
-- ANSWER:
def sorted : list ℕ → bool 
  | [] := tt
  | [(x : ℕ )] := tt
  | (x :: y :: L) := leq x y && sorted (y :: L)


-- DO NOT DELETE:
example: sorted [] = tt := begin refl, end 
example: sorted [1] = tt := begin refl, end 
example: sorted [1,2,3,4,5] = tt := begin refl, end 
example: sorted [0,0,0,0] = tt := begin refl, end 
example: sorted [3,4,1] = ff := begin refl, end 
example: sorted [1,2,3,4,1] = ff := begin refl, end 


/- HWK04-16-3: 
a "sorting program" is any function f : list ℕ → list ℕ. suppose that f is a sorting program. formalize the following english statement in LEAN: "f always produces sorted lists, i.e., lists on which the function sorted defined above returns tt". (you can ignore the "section" stuff) 
-/
-- ANSWER:
section hwk04_16_3
variable f : list ℕ → list ℕ
#check ∀ x : list ℕ, sorted (f x) = tt
end hwk04_16_3


/- HWK04-16-4: 
let's label by (srt) the property for f that you provided in HWK04-16-3. is (srt) sufficient to express correctness of f, or are there sorting programs f that satisfy (srt) but which are wrong according to our expectations of what a correct sorting program should output? if you answer "yes" to the last question (meaning "yes, there are sorting programs f that satisfy (srt) but which are still wrong"), exhibit at least one counterexample (i.e., a function f which satisfies (srt) but which is not a correct sorting function). you can write your answer inside this comment, but if you provide a function f, provide it outside the comment:

-- ANSWER:
  There is no sorting program f which satisfy srt but is wrong according to our definition of correct because it checks for empty list, or a list of only one element. Then it checks if the first two elements are sorted and uses the second one and the one after to check if the rest of the list is correct recursively. Due to transitive property, the definition will return tt for any list that is sorted.
-/






/- HWK04-17:
in class we claimed that IMPLICATION is the most important logical operator, in the sense that all other logical operators can be defined in terms of implication. show this. 

in particular, consider the boolean functions negb, andb, orb:
-/

def negb : bool -> bool 
    | tt := ff 
    | ff := tt 
--

def andb : bool -> bool -> bool 
    | ff _ := ff 
    | tt x := x 
--

def orb : bool -> bool -> bool 
    | tt _ := tt 
    | ff x := x 
--


/- HWK05-17-1:

define the boolean implication function impliesb using pattern matching and only two nonoverlapping cases (follow the truth table for implication in the slides for propositional logic!):
-/

-- ANSWER:
def impliesb : bool -> bool -> bool 
    | ... 
    | ... 



/- HWK05-17-2:

define boolean not in terms of boolean implication. that is, define the function negbwithimplies : bool -> bool such that:
    (1) negbwithimplies is not defined with pattern matching, but by calling impliesb with appropriate arguments (including constants like tt or ff). negbwithimplies can only call impliesb! it can call impliesb as many times as it wants. it cannot call andb, orb, or any LEAN  function. 

    (2) negbwithimplies is equivalent to negb. prove that in LEAN. 
-/
-- ANSWERS:

def negbwithimplies (x : bool) : bool := ... 

theorem negbwithimplies_equiv_negb: 
    ∀ x : bool, negbwithimplies x = negb x 
:= begin
    ... 
end


/- HWK05-17-3:

define boolean or in terms of boolean implication. that is, define the function orbwithimplies : bool -> bool -> bool such that:
    (1) orbwithimplies is not defined with pattern matching, but by only calling impliesb with appropriate arguments (same rules as in HWK05-17-2 apply). 

    (2) orbwithimplies is equivalent to orb. prove that in LEAN. 
-/
-- ANSWERS:

def orbwithimplies (x y : bool) : bool := ... 

theorem orbwithimplies_equiv_orb: 
    ∀ x y : bool, orbwithimplies x y = orb x y 
:= begin
    ... 
end



/- HWK05-17-4:

define boolean and in terms of boolean implication. that is, define the function andbwithimplies : bool -> bool -> bool such that:
    (1) andbwithimplies is not defined with pattern matching, but by only calling impliesb with appropriate arguments (same rules as in HWK05-17-2 apply). 

    (2) andbwithimplies is equivalent to andb. prove that in LEAN. 
-/
-- ANSWERS:

def andbwithimplies (x y : bool) : bool := ... 

theorem andbwithimplies_equiv_andb: 
    ∀ x y : bool, andbwithimplies x y = andb x y 
:= begin
   ... 
end




/- HWK04-18:
Give:
    1. at least 3 different examples of _valid_ propositional logic formulas (tautologies) 
    2. at least 3 different examples of _unsatisfiable_ propositional logic formulas
    3. at least 3 different examples of propositional logic formulas which are both _satisfiable_ and _falsifiable_

Write your answer as valid LEAN code in the "..." below, using the predefined variables p, q, r (you cannot add more variables, you can only use those 3). Your formulas should be of type Prop, not bool. you can use "true" and "false" as subformulas. 

For example, "false" is a correct answer for an unsatisfiable formula and "true" is a correct answer for a valid formula. Also, both "p" and "q" are both satisfiable and falsifiable. Do not give any of those four answers. You have to come up with different ones. 
-/


-- ANSWER:
section hwk04_18

variables p q r : Prop 

-- 3 valid formulas (tautologies):
#check ... 
#check ... 
#check ... 

-- 3 unsatisfable formulas:
#check ... 
#check ... 
#check ... 


-- 3 satisfiable and falsifiable formulas:
#check ... 
#check ... 
#check ... 


end hwk04_18

