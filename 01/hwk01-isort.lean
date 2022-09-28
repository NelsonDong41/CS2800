-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


/-

Your first proof assignment! Insertion sort is a simple sorting method. Consider the implementation of insertion sort in LEAN below. Prove, using any method of your choice, that this implementation is correct. You have to do three things:
    (1) State clearly what you mean by "correct". 
    (2) Prove correctness.
    (3) Check whether your definition of "correct" is "complete".     If it is, then buggy implementations should not satisfy your definition of "correct". Provide at least two buggy implementations and argue why they are buggy and where they fail your proof. 

This assignment in intentionally open-ended. The goal is to make you think what a "proof" is. We are not expecting you to write proofs in LEAN, although if you want to try, please do! We are also not necessarily expecting mathematical proofs. Ultimately, a proof is an argument that tries to convince somebody about something. Try to convince yourself that this code is correct. Try to convince us as well. At the end of the semester, you can go back and compare the formal proofs (including of insertion sort!) that we will have done by then, to the answers you gave in this first assignment. Then you will appreciate better what a formal proof is.

However, we do expect some reasonable amount of thought in your answers. We will cut points for generic answers like this:
"A "correct" implementation of an algorithm will always produce correct, expected solutions for valid input instances of the problem."

Provide a single PDF file with your answers. 

This assignment is individual (one answer per student, no groups).

-/

def insrt : ℕ → list ℕ → list ℕ
-- insrt is a function that takes as input a natural number (i.e., of type ℕ),
-- and a list of natural numbers, and returns as output a list of natural numbers
  | x [] := [x] -- if the input number is x and the input list is empty,
                -- then return the list [x] (that contains just the number x)
  | x (y :: L) := if (x ≤ y) -- if the input list has head y and tail L, and x <= y
                  then x :: (y :: L) -- then return the list [x, y, elements of L]
                  else y :: (insrt x L) -- else return the list with head y and tail 
                                        -- the list that (insrt x L) returns

#eval insrt 1 [1,2,3]
#eval insrt 10 [1,2,3]
#eval insrt 10 [1, 2, 30]
#eval insrt 10 [100,50,0,20]


def isort : list ℕ → list ℕ
-- isort is a function that takes a list of nats and returns a list of nats
  | [] := []  -- if the input list is empty, return the empty list
  | (x :: L) := insrt x (isort L) -- otherwise, sort the tail L, and then insert the head x in the sorted tail

#eval isort [2,1,4,1,3,5,1,2] -- move cursor here to see result
#eval isort [3,1,3,4,5,1,1,0,2,3,4,2,3,6,3,45,3,0,4,5,1,3,4]
example: isort [3,1,3,4,5,1,1,0,2,3,4,2,3,6,3,45,3,0,4,5,1,3,4] =
[0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 6, 45]
:= begin refl, end