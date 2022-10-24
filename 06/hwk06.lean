-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 6

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Alyssa Mui, Nelson Dong, Justin Pong
-/

/-
Technical instructions: same as in the last homework, PLUS ADDITIONAL INSTRUCTIONS BELOW:
-/



/- ADDITIONAL INSTRUCTIONS:

Just like you are welcome to use any function defined in class or in previous homeworks or in the current homework, you are also welcome to use any lemma/theorem/example proved in class or in previous homeworks or in the current homework. 

You are also allowed to define and use your own helper functions and you are also allowed to define and use/"call" your own lemmas/theorems, in order to prove other theorems. 

WE WILL CUT POINTS OFF IF YOU USE classical.em or classical.by_contradiction UNNECESSARILY.  

-/

import .ourlibrary11


/- HWK06-01:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem not_false_true: ¬ false ↔ true 
-- ANSWER: The theorem is true.
:= begin
  split,
  repeat {
    dunfold not,
    intros,
    trivial,
  }
end


/- HWK06-02: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem xor_commut: ∀ P Q : Prop, (xor P Q) ↔ (xor Q P) 
-- ANSWER: This theorem is true.
:= begin
  intros,
  split, 
  repeat {
    intros h,
    rw xor at h,
    rw xor,
    cases h,
    {
      right,
      assumption
    },
    {
      left,
      assumption
    }
  },
end 


/- HWK06-03: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_implies_xor: ∀ p q : Prop, p → ((xor p q) ↔ ¬q)
-- This theorem is true.
-- example: ∀ p q : Prop, p_implies_xor p q = false := begin refl, end
:= begin
  intros p q h,
  split,
  {
    dunfold xor,
    dunfold not,
    intros h2 h3,
    cases h2,
    repeat {
      cases h2 with h4 h5,
      {
        trivial,
      }
    }
  },
  {
    dunfold xor,
    dunfold not,
    intros h2,
    left,
    split,
    {
      assumption
    },
    {
      assumption
    } 
  }
end


/- HWK06-04: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem and_elim: ∀ p q r : Prop, (p ∧ q) → (p → q → r) → r 
-- ANSWER:
:= begin
  intros p q r h1 h2,
  cases h1,
  {
    have h3 := h2 h1_left,
    have h4 := h3 h1_right,
    assumption,
  }
end



/- HWK06-05: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem or_elim: ∀ p q r : Prop, (p ∨ q) → (p → r) → (q → r) → r 
-- ANSWER:
:= begin
  intros p q r h h1 h2,
  cases h,
  {
    have h3 := h1 h,
    assumption
  },
  {
    have h3 := h2 h,
    assumption
  }
end



/- HWK06-06: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/

theorem not_p_not_q_iff: ∀ P Q : Prop, ¬ P → ¬ Q → (P ↔ Q) 
-- This theorem is false when P = true and Q = false


/- HWK06-07: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem mp_eq: ∀ P Q : Prop, ((P → Q) ∧ P) ↔ (P ∧ Q) 
-- ANSWER: This theorem is true.
:= begin
  intros p q,
  split, {
    intros h,
    cases h, {
      split,
      {
        assumption
      } ,
      {
        have h1 := h_left h_right,
        assumption
      }   
    }
  },
  {
    intros h,
    cases h, {
      split, {
        intro,
        assumption,
      },
      {
        assumption
      }
    },
  }
end


/- HWK06-08: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem contraposition: ∀ P Q : Prop, (P → Q) → (¬ Q → ¬ P) 
-- ANSWER: This theorem is true.
:= begin
  intros p q h1 h2,
  dunfold not,
  intro h3,
  have h4 := h1 h3,
  trivial,
end


/- HWK06-09: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem iff_and: ∀ P Q : Prop, (P ↔ Q) ↔ ((P → Q) ∧ (Q → P))
-- ANSWER: This theorem is true.
:= begin
  intros p q,
  split, {
    intro h,
    cases h with h1 h2,
    {
      split,
      repeat {
        assumption
      }
    }
  }, {
    intro h,
    split,
    repeat {
      cases h, {
        assumption
      }
    }
  }
end

/- HWK06-10: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem implies_trans: ∀ A B C : Prop, (A → B) ∧ (B → C) → (A → C)
-- ANSWER: This theorem is false. (A B C) is (T F T) or (F T F)



/- HWK06-11: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/

-- from 10-code.lean
theorem true_implies_p: ∀ P : Prop, (true → P) ↔ P := begin
    intro,
    split,
    {
        intro h,
        -- now what? we have true → P as an assumption. we know that true holds, so we could use modus ponens to get P. but even if we know that true holds, we don't have a proof of true in our list of hypotheses! how do we get one? like this:
        have h1 : true -- we state that we will prove "true"
        := begin -- we begin the proof-within-the-proof
            trivial, -- we prove it
        end, -- we end the proof-within-the-proof, and we now have h1 : true in our list of hypotheses!
        
        -- this "have" pattern with a begin ... end proof section is very useful because we can have proofs within proofs. but try not to abuse this feature: if the proof within a proof gets too long, it means you should probably separate it into a lemma (modularity & reuse principle).

        have h2 := h h1,
        assumption,
    },
    {
        intro h1,
        intro h2,
        assumption,
    }
end

theorem p_xor_true: ∀ P : Prop, (xor P true) ↔ ¬ P 
-- ANSWER: This theorem is true.
:= begin
  intros,
  rw xor,
  split,
  {
    intro h,
    cases h,
    {
      dunfold not,
      dunfold not at h,
      cases h,
      {
        rw true_implies_p at h_right,
        trivial,
      }
    },
    {
      cases h,
      {
        assumption
      }
    }
  },
  {
    intro h,
    {
      right,
      split,
      {
        trivial,
      },
      {
        assumption
      }
    }
  }
end



/- HWK06-12: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_xor_not_p: ∀ P : Prop, xor P ¬P 
-- This theorem is true.
:= begin
  intros,
  dunfold xor,
  dunfold not,
  have h1 := classical.em P,
  cases h1 , {
    left,
    split, {
      assumption,
    },
    {
     intro h2,
     have h3 := h2 h1,
     assumption,
    }
  },
  {
    dunfold not at h1,
    right,
    split, 
    repeat {
      assumption,
    }
  }
end


/- HWK06-13-1: 
prove the following in two ways:

1. directly, without calling any other lemmas/theorems. 
-/
example: ∀ x : nat, x = 0 ∧ x ≠ 0 → x > 10 
:= begin
-- ANSWER: direct proof
  intros x h,
  cases x,
  repeat {
    cases h,
    {
      contradiction,
    }
  }
end

/- HWK06-13-2: 
2. by calling a lemma/theorem that we proved already in class. you must find which lemma or theorem you want to use among those that we proved in class already. read the lecture code and decide. copy the lemma/theorem that you chose here, and then use it. 
-/
-- ANSWER: proof using the following result proven in class:
#check ∀ x : nat, x = 0 ∧ x ≠ 0

-- (P ∧ (not P))

-- from 09-code.lean
theorem not_p_and_not_p: ∀ P : Prop, ¬ (P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    -- now recall that ¬P is the same as P → false:
    dunfold not at h2,
    -- therefore, we can apply modus ponens:
    have h3 : false := h2 h1,
    trivial,
end

example: ∀ x : nat, x = 0 ∧ x ≠ 0 → x > 10 
:= begin
-- ANSWER:
  intros x h,
  have h1 := not_p_and_not_p (x = 0),
  trivial,
end




/- HWK06-14: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
example: ∀ x y : ℕ, x = y+1 → x > 0 → (x > 0 ∧ y+1 > 0) 
-- ANSWER: This is true.
:= begin
  intros x y h1 h2,
  split,
  {
    assumption,
  },
  {
    cases x,
    {
      cases y,
      {
        contradiction
      },
      {
        contradiction
      } 
    },
    {
      rw h1 at h2,
      assumption,
    }
  }
end


/- HWK06-15-1: 
a classic equivalence in (classical) logic is that (p → q) is equivalent to (¬p ∨ q). we will prove this in two steps. one (and only one!) of these steps requires the law of excluded middle. which one?

first, prove the following. did you have to use classical.em?
-/

theorem p_implies_q_implies_not_p_or_q: 
    ∀ p q : Prop, (p → q) → (¬p ∨ q) 
:= begin
-- ANSWER:  
-- Yes we had to use classical.em
  intros p q h,
  have h2 := classical.em p,
  cases h2, {
    have h3:= h h2,
    right,
    assumption
  },
  {
    left,
    assumption
  } 
end


/- HWK06-15-2: 
now, prove the following. did you have to use classical.em? No
-/
theorem not_p_or_q_implies_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) → (p → q)
:= begin
-- ANSWER:  
  intros p q h h1, 
  dunfold not at h,
  cases h,
  {
    have h2 := h h1,
    trivial,
  },
  {
    assumption
  }

end


/- HWK06-16: 
prove the following. did you have to use classical.em? (answer YES/NO to the latter question). 
-/
lemma and_absorb_or_and: ∀ p q : Prop, p ∧ (¬ p ∨ q) ↔ (p ∧ q) 
:= begin
-- ANSWER: I didn't use classical.em
  intros x y,
  split,
  {
    dunfold not,
    intros h,
    cases h with h1 h2,
    {
      split,
      {
        assumption,
      },
      {
        cases h2,
        {
          contradiction,
        },
        {
          assumption,
        }
      }
    }
  },
  {
    dunfold not,
    intros h,
    split,
    {
      cases h,
      {
        assumption,
      },
    },
    {
      right,
      cases h,
      {
        assumption,
      }
    }
  }
end




/- HWK06-17-1: 
the famous _De Morgan's laws_ of propositional logic state that:

  1. ¬ (p ∨ q) is equivalent to (¬ p) ∧ (¬ q) 
  2. ¬ (p ∧ q) is equivalent to (¬ p) ∨ (¬ q) 

thou shalt (you shall) prove these laws. we will first split each equivalence into two implications, so you will first have 4 separate lemmas to prove. try to prove as many of those 4 as you can using only constructive logic, that is, _without_ using classical.em, nor classical.by_contradiction. how many and which ones did you manage to prove without these axioms?
-/

lemma deMorgan1: ∀ (p q : Prop), (¬ p ∧ ¬ q) → ¬ (p ∨ q) 
:= begin
-- ANSWER:
  intros p q h,
  intro h1,
  cases h1,
  repeat {
    cases h,
    {
      trivial,
    }
  },
end


lemma deMorgan2: ∀ (p q : Prop), (¬ p ∨ ¬ q) → ¬ (p ∧ q) 
:= begin
-- ANSWER:
  intros p q h,
  dunfold not,
  cases h,
  {
    dunfold not at h,
    intro h2,
    cases h2 with h3 h4,
    {
      have h5 := h h3,
      assumption,
    },
  },
  {
    dunfold not at h,
    intro h2,
    cases h2 with h3 h4,
    {
      have h5 := h h4,
      assumption
    }
  }
end

theorem p_and_q_implies_q_with: ∀ p q : Prop, (p ∧ q) → q 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    exact h2, 
end

lemma deMorgan3: ∀ (p q : Prop), ¬ (p ∨ q) → (¬ p ∧ ¬ q) 
:= begin
-- ANSWER:
  intros p q h,
  
  
end

theorem p_and_q_implies_p: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    assumption,
end


theorem modus_ponens: ∀ P Q : Prop, ((P → Q) ∧ P) → Q 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,  -- we can use cases with renaming the labels to what we want
    -- at this point we know that P is true, and also that P → Q is true. how can we derive Q from these two hypotheses?
    have h3 : Q := h1 h2, /- the _have_ tactic allows to add new hypotheses in the list of hypotheses. here we are adding a new hypothesis, namely, that Q holds. h3 can be seen as just a label for this new hypothesis. but given what we said above, h3 can also be seen as a proof that Q holds. now, we cannot just add whatever hypothesis we want without justification. this would render our proof system useless (in fact, unsound). therefore, whenever we claim to have found say h3 of type Q, we _must_ provide a proof for Q. in other words, we must define the proof h3. we do that using := followed by either "begin ... end" and the usual tactics that we know, or by application of other known facts, as in the example above. 
    -/
    -- now that we have derived Q in the hypotheses, we can conclude the proof:
    assumption,
end

lemma deMorgan3b: ∀ (p q : Prop), ¬ (p ∨ q) → (¬ p ∧ ¬ q) 
:= begin
-- ANSWER:
  intros p q h,
  split,
  {
    dunfold not,
    have h2 := classical.em (¬ (p ∨ q) → (¬ p ∧ ¬ q)),
    cases h2, {
      dunfold not at h2,
      dunfold not at h,
      have h3 := h2 h,
      cases h3, {
        trivial,
      }
    }, {
      dunfold not at h2,
      dunfold not at h,
    }
    
    
  },
  {

  }
  
end

theorem disjunction_right: ∀ P Q : Prop, Q → (P ∨ Q) 
:= begin
    intro,
    intro,
    intro,
    right,      -- we choose to prove the right part of the disjunction
    assumption,
end


theorem modus_ponens_with_implications: ∀ P Q : Prop, P → ((P → Q) → Q) 
:= begin
    intro, 
    intro,
    intro h1, 
    intro h2,   
    have h3 := h2 h1,  -- the type Q of H3 can be omitted 
    assumption,
end


lemma deMorgan4: ∀ (p q : Prop), ¬ (p ∧ q) → (¬ p ∨ ¬ q) 
:= begin
-- ANSWER:
  intros p q h,
  dunfold not,
  dunfold not at h,
  right,
  have h1 := p_and_q_implies_q_with p q,
  have h2 := disjunction_right p q,
  rw h1 at h2,
  intro h3, 
  have h6 := classical.em q,
  have h7 := classical.em p,
  have h4 := h2 h3,
  have h5 := modus_ponens_with_implications (p ∨ ¬ p) false h7,
  have h10 := not_p_and_not_p p,
  dunfold not at h10,
  have h9 := classical.em,
  
end


/- HWK06-17-2: 
combine the 4 lemmas above to prove the two deMorgan theorems below (in this problem we are not asking you to re-do the proofs by copy-pasting everything you already wrote above, but instead to call the above lemmas at the appropriate places in your proof):
-/
theorem deMorgan_or: ∀ p q : Prop, ¬ (p ∨ q) ↔ (¬p ∧ ¬q)
:= begin
-- ANSWER:
  intros p q,
  split, {
    have h1 := deMorgan3 p q,
    assumption,
  },
  {
    have h1 := deMorgan1 p q,
    assumption,
  }
end


theorem deMorgan_and: ∀ p q : Prop, ¬ (p ∧ q) ↔ (¬p ∨ ¬q) 
:= begin
-- ANSWER:
  intros p q,
  split, {
    have h1 := deMorgan4 p q,
    assumption,
  },
  {
    have h1 := deMorgan2 p q,
    assumption,
  }
end




/- HWK06-18: 
the theorems "le_transitive" and "lt_implies_le" below are given to you. you don't need to know how they have been proven. consider them part of some "black-box" library. you can call stuff from that library, but you don't need to know how they are implemented. 

use these theorems to prove theorem "hwk06_18": 
-/

theorem le_transitive: ∀ x y z : ℕ, x ≤ y → y ≤ z → x ≤ z 
:= begin
    intro,
    intro,
    intro,
    intro h1,
    intro h2,
    apply nat.le_trans h1 h2,
end

theorem lt_implies_le: ∀ x y : ℕ, x < y → x ≤ y 
:= begin
    intro,
    intro,
    intro h,
    apply le_of_lt h,
end

theorem hwk06_18: ∀ a b c : ℕ, (a < b ∧ b < c) → a ≤ c 
:= begin
-- ANSWER:
   intros a b c h,
   cases h, {
     have h1 := lt_implies_le a b,
     have h2 := lt_implies_le b c,
     have h3 := h1 h_left,
     have h4 := h2 h_right,
     have h5 := le_transitive a b c,
     have h6 := h5 h3 h4,
     assumption,
   }
end


/- HWK06-19: 
consider the following functions:
-/

def len : list nat -> nat 
  | [] := 0
  | (_ :: L) := (len L) + 1 
--

def app : list nat -> list nat -> list nat 
  | [] L := L 
  | (a :: L1) L2 := a :: (app L1 L2)
--

def tail: list nat -> list nat 
  | [] := []
  | (x :: L) := L
--

def minus1: nat -> nat 
    | 0 := 0 
    | (nat.succ x) := x 
--



/- HWK06-19-1:
write the LEAN theorem "len_tail_or" stating that for any list of nats L, either L is empty and the length of the tail of L is zero, or the length of the tail of L is one less than the length of L. use the "minus1" function above to express "one less". use "or" (and not "xor") to combine the two parts. 

then prove the theorem "len_tail_or". 
-/
-- ANSWER:
theorem len_tail_or: ∀ L : list ℕ , ((len L) = 0 ∧ (len (tail L) = 0)) ∨ ((len (tail L)) = minus1 (len L))
:= begin
  intros,
  cases L, 
  {
    dunfold len,
    dunfold tail,
    dunfold minus1,
    left,
    rw len,
    split, repeat {
      refl
    }
  },
  {
    dunfold len,
    dunfold tail,
    dunfold minus1,
    right,
    refl
  }
end

/- HWK06-19-2:
does the statetement hold if we use "xor" instead of "or"? if yes, prove it also with "xor". if not, provide a counterexample. 
-/
-- ANSWER: no.

/-
if L = [], then len [] = 0 and len (tail []) = 0 is true,
and len (tail []) = 0
 and minus1 (len []) -> minus1 0 -> 0 so 0 = 0
 and then 
 len [] = 0 ∧ len (tail []) = 0 is true,
 so (xor true true) is false and the theorem is false
-/