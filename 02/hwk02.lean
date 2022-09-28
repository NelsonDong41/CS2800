-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 2


/-
This homework is done in groups. Doing the homework in groups does not mean you split the problems among members of the group. EVERY member of the group should try to do ALL problems. Then you meet and compare notes. Help each other. If you cannot solve a problem, ask your team mates, but only after you tried it yourself.

 * Groups should consist of 2-3 people.
 * Homework is submitted by only one person per group. Therefore make sure the person responsible for submitting actually does so. If that person forgets to submit, your team gets 0.
 * Submitting the homework: please await further instructions. Start doing the homework now though!
 * You must list the names of ALL group members below, using the given format. This way we can confirm group membership with the Canvas groups.  If you fail to follow these instructions, it costs us time and it will cost you points, so please read carefully.

The format should be: FirstName1 LastName1, FirstName2 LastName2, ...
For example:
Names of ALL group members: Aretha Franklin, Billy Holiday, Frank Sinatra

There will be a 10 pt penalty if your names do not follow this format.

Replace "..." below with the names as explained above.

Names of ALL group members: ...
-/

/-
Technical instructions:
- Open this file in LEAN. Some of the lines in this file are very long. You can enable "wrap line" under "View -> Toggle Word Wrap" in VS Code, so that you don't have to scroll left-right to see the entire line. 
- Insert your solutions into this file where indicated (usually as "..."). Sometimes we require textual explanations. In that case insert your answer in LEAN comments like these. 
- Make sure the entire file is accepted by LEAN (no red underlines, except when we specifically allow it). In particular, there must be no "..." left in the code. If you don't finish all problems, comment the unfinished ones out. 
- Only add to the file. Do not remove or comment out anything pre-existing (except the ..., which you will replace with your answers).
- Unless otherwise stated, when asked to define a function, you must specify all the types (both inputs and outputs) in the signature of the function yourself, rather than letting LEAN infer the types. For example, you should define your function like that:
    def f (x : nat) : nat := x+1
  and not like that:
    def f (x : nat) := x+1
  or like that:
    def f := fun x, x+1
  It's always OK to use ℕ instead of nat, ℤ instead of int, → instead of ->, etc. 
- Unless otherwise stated, you are NOT allowed to use any "non-trivial" LEAN library functions that you discovered somehow. You can certainly use predefined operators like +, *, etc, constants like 0, 1, ..., the empty list [], ::, list.cons, etc. But for example, you are not allowed to use the predefined _append_ function or the predefined list.length function, etc.
- Feel free to define "helper functions" if you need them. A "helper function" is a function that you define and call from your "main" function / solution to the problem. 
- When done, save your file WITHOUT renaming it. 
-/





/- HWK02-01:
Define the function "multiply" which takes two natural numbers and returns their product (multiplication). You can use LEAN's predefined "*" operator in your definition. 
Evaluate your function on a number of examples using #eval. 
Make sure you can write down the type of multiply without help from LEAN. 
-/
-- ANSWER:
def multiply ...
#eval multiply 0 3
#eval multiply 13 5
...


/- HWK02-02:
Define the function "divide" which takes two natural numbers x and y, and divides them, returning x/y. The result should be an integer number. If y=0 your function should return -1. Otherwise it should return x/y rounded down, so that (divide 3 2) for example should return 1 and (divide 2 3) should return 0. You can use LEAN's predefined "/" operator in your definition. 
Evaluate your function on a number of examples.
-/
-- ANSWER:
def divide ...
#eval divide 3 1
#eval divide 3 2
#eval divide 2 3
#eval divide 3 0
...


/- HWK02-03:
Define a function called "diff_by_one" which takes two natural numbers x and y, and returns a bool, tt ("true") if either x = y+1 or y = x+1, and ff ("false") otherwise. 
NOTE: Do NOT use a logical OR operator (no "||", "or", "∨", etc). 
HINT: you can do it by using if-then-elses (possibly nested). 
CHALLENGE: try to do it without if-then-else, using pattern matching only (recursion is OK). 
Evaluate your function on a number of examples.
-/
-- ANSWER:
def diff_by_one ...
#eval diff_by_one 3 1
#eval diff_by_one 3 2
#eval diff_by_one 3 5
#eval diff_by_one 3 4
... 


/- HWK02-04-1:
Write down in the place of "..." the type of the function given below. 
NOTE: THINK and come up with the answer yourself, without using #check. Then you can confirm your answer using #check. In the exams you may not have access to LEAN. You will be expected to be able to read LEAN code and come up with the types of functions "manually".
-/
def f (b : bool) (x : nat) := if (b = tt) then (x:int) else (-x:int)
-- ANSWER:
-- The type of f is ... 

/- HWK02-04-2:
Write the same function as f above, but as an anonymous (lambda) function. f and your anonymous definition of it must be equivalent, meaning they should have the same type and also return the same result, for every input. 
-/
#check fun ... 



/- HWK02-05:
For each of the expressions below, write in the place of "..." whether the expression is well-typed or not, i.e., whether it results in a type error. f is the function defined right above.
NOTE: THINK and come up with the answer yourself, without using LEAN. Then you can confirm your answer using LEAN. In the exams you may not have access to LEAN. You will be expected to be able to read LEAN code and come up with the answer to questions like this "manually".
 f 0 tt           -- ... 
 f tt 0           -- ... 
 f 0              -- ... 
 f tt             -- ... 
 f (0 tt)         -- ... 
 (f 0) tt         -- ... 
 (f 0 tt)         -- ... 
 ((f) (0) (tt))   -- ... 
 (f 0) (tt)       -- ... 
 f (f 10 tt) tt   -- ... 
 f (f 10 ff) tt   -- ... 
 (f 10 tt) + 1    -- ... 
 (f 10 ff) + 1    -- ... 
-/



/- HWK02-06:
Redefine the function f from HWK02-04 using pattern-matching. Call the new function fg. fg should be equivalent to f, meaning that (1) it should have the same type as f, and (2) for every input, both f and fg should return exactly the same output. 
-/
-- ANSWER:
... 


/- HWK02-07:
Define the function "factorial" which takes a nat x and computes x!, the factorial of x. Recall that x! = x * (x-1) * ... * 1 if x>0 and that 0! = 0. Define the function "from scratch" using only addition, multiplication and recursion (no other predefined LEAN operations).  
-/
-- ANSWER:
... 


/- HWK02-08:
Define the function "fib" which takes as input a nat n and returns as output the n-th Fibonacci number. Recall that the Fibonacci sequence is: 0, 1, 1, 2, 3, 5, 8, 13, ..., and that each number in the sequence is obtained by adding the previous two numbers in the sequence. So, (fib 0) = 0, (fib 1) = 1, (fib 2) = 1, (fib 3) = 2, etc. 
-/
-- ANSWER:
...


/- HWK02-09:

is this function terminating? if it is, is LEAN able to prove that it's terminating?

def sumallint : int -> int  
  | 0 := 0
  | n := n + (sumallint (n-1)) 

independently of the answers you gave in the two questions above, use the transformation trick we provided in class to transform the above function into a terminating function called sumallintbounded. 

-/
-- ANSWER:

... 



/- HWK02-10:
Define the function "compose" that takes as input two functions f : ℕ → bool and g : bool → ℤ and composes them, yielding a function h : ℕ → ℤ such that (h x) = g (f x). 
Make sure you can write down the type of compose without help from LEAN. 
-/
-- ANSWER:
def compose ... 



/- HWK02-11:
Define the function "genzeros" which takes a nat n and returns a list of n zeros. For example, (genzeros 3) should return [0,0,0] and (genzeros 0) should return [].
-/
-- ANSWER:
def genzeros ... 

#eval genzeros 0
#eval genzeros 3




/- HWK02-12:
Define the function "app" which takes as input two lists of nats and concatenates them, that is, appends the second after the first one. For example (app [1,2,3] [3,4,5]) should return [1,2,3,3,4,5]. Define the function recursively, and not using LEAN's library function "append".  
-/
-- ANSWER:
def app  ... 
  
  


/- HWK02-13:
Define the function "apply" which takes as input a list of nats L = [x1,x2,...] and a function f : ℕ → ℕ, and returns the list L' = [(f x1), (f x2), ...], that is, it applies f to all the elements of L. 

Evaluate your function on a number of examples using the empty list [] and the list [0,1,2,3], and passing the second argument f the anonymous (lambda) functions that multiply their input by 3, and add 42 to their input. Also evaluate on the same lists where f is the Fibonacci function. 

Then define the function "apply2int" which is the same as "apply", except that its argument f has type ℕ → ℤ, and therefore its output list L' has type list ℤ. Observe what happens when you call "apply2int" with exactly the same arguments as in the examples we requested for "apply", above. Finally, use "apply2int" and the lambda function you defined in HWK02-04-2 to turn the list of nats [0,1,2,3] into the list of ints [0,-1,-2,-3] (this should be a single #eval call). 
-/
-- ANSWER:

def apply : ...

#eval apply [] ...
#eval apply [] ...
#eval apply [] ...

#eval apply [0,1,2,3] ...
#eval apply [0,1,2,3] ...
#eval apply [0,1,2,3] ...

def apply2int : ... 

#eval apply2int [0,1,2,3] ...    -- result should be [0, -1, -2, -3]



/- HWK02-14:
The serial composition of two functions f : A → B and g : B → C, is the function f ∘ g : A → C, such that (f ∘ g) x = g (f x). 

Define the function _serialcompo_ which takes as input a list of functions L = [f1,f2,...], where each function fi is from ℕ to ℕ, returns the serial composition f1 ∘ (f2 ∘ (f3 ∘ ...)). 
If the input list is empty, then _serialcompo_ should return the identity function (λ x : nat, x). If the input list has only one element f, then _serialcompo_ should return f. 

Evaluate your function on the examples given below:
-/
-- ANSWER:

def serialcompo ... 

#eval serialcompo [] 123 
#eval serialcompo [fib] 10 
#eval serialcompo [nat.mul 2, nat.add 0, fib] 10


