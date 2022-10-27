theorem or_assc: forall A B C : Prop, or A (or B C) <-> or (or A B) C
:= begin
  intros,
  split,
  {
    intro h,
    cases h,
    {
      left,
      left,
      assumption
    },
    {
      cases h,
      {
        left,
        right,
        assumption
      },
      {
        right,
        assumption
      }
    }
  },
  {
    intro h,
    cases h,
    {
      cases h,
      {
        left,
        assumption
      },
      {
        right,
        left,
        assumption
      }
    },
    {
      right,
      right,
      assumption
    }
  }
end


theorem and_distrib_or: ∀ A B C : Prop, and A (or B C) <-> or (and A B) (and A C)
:= begin
  intros,
  split,
  {
    intro h,
    cases h with h1 h2,
    {
      cases h2,
      {
        left,
        split,
        repeat {
          assumption
        }
      },
      {
        right,
        split,
        repeat {
          assumption
        }
      }
    }
  },
  {
    intro h,
    cases h,
    {
      cases h,
      {
        split,
        {
          assumption
        },
        {
          left,
          assumption
        }
      }
    },
    {
      cases h,
      {
        split,
        {
          assumption
        },
        {
          right,
          assumption
        }
      }
    }
  }
end


theorem not_p_implies_xor: forall p q : Prop, (not p) -> ((xor p q) <-> q)
:= begin
  intros p q h,
  split,
  {
    intro h1,
    cases h1,
    {
      have h2 := classical.em q,
      cases h2,
      {
        assumption
      },
      {
        cases h1,
        {
          contradiction
        }
      }
    },
    {
      cases h1,
      {
        assumption
      }
    }
  },
  {
    intro h2,
    dunfold xor,
    {
      right,
      split,
      repeat {
        assumption
      }
    }
  }
end


lemma not_true_false: (not true) <-> false
:= begin
  split,
  {
    intros h,
    dunfold not at h,
    have h1 : true := trivial,
    have h2 := h h1,
    assumption
  },
  {
    trivial
  }
end

theorem not_xor_p_p: forall P : Prop, not (xor P P)
:= begin
  intros,
  intro h,
  cases h,
  repeat {
    cases h,
    {
      contradiction
    }
  }
end


#check nat.left_distrib 
#check nat.le_add_right 

example: forall x y z w : nat, x * (y + z) <= (x * y + x * z) + w
:= begin
  intros,
  have h := nat.left_distrib x y z,
  rw h,
  have h2 := nat.le_add_right (x * y + x * z) w,
  assumption
end

lemma cancelsucc: forall x y : nat, (nat.succ x) = (nat.succ y) -> x = y 
:= begin
  intros x y h ,
  simp at h,
  assumption,
end

def plus : nat -> nat -> nat
  | nat.zero y := y
  | (nat.succ x) y := nat.succ (plus x y)

example: forall x : nat, 
  not(x = plus x 1) -> not (nat.succ x = plus (nat.succ x) 1)
  := begin
    intros x h,
    rw plus,
    intro h1,
    have h2 := cancelsucc (x) (plus x 1),
    have h3 := h2 h1,
    contradiction
  end

inductive ternary : Type 
  | ttt : ternary   -- true 
  | fff : ternary   -- false
  | mbe : ternary   -- maybe 
  
open ternary 

def tnot : ternary -> ternary 
  | ttt := fff 
  | mbe := mbe 
  | fff := ttt 

def tand : ternary -> ternary -> ternary 
  | ttt x := x
  | mbe ttt := mbe 
  | mbe mbe := mbe 
  | mbe fff := fff 
  | fff _ := fff 

def tor : ternary -> ternary -> ternary 
  | ttt x := ttt 
  | mbe ttt := ttt 
  | mbe mbe := mbe 
  | mbe fff := mbe 
  | fff x := x 

theorem deMorgan_tand: forall x y : ternary,
  tnot (tand x y) = tor (tnot x) (tnot y)
:= begin
  intros,
  cases x,
  repeat {
    cases y,
    repeat {
      dunfold tand,
      dunfold tnot,
      dunfold tor,
      refl,
    }
  }
end


def timp : ternary → ternary → ternary 
  | ttt x := x
  | fff _ := ttt
  | mbe ttt := ttt
  | mbe fff := mbe
  | mbe mbe := mbe

theorem timp_tor: forall x y : ternary, 
  timp x y = tor (tnot x) y
:= begin
  intros,
  cases x,
  repeat {
    cases y,
    repeat {
      rw timp,
      rw tnot,
      rw tor,
    }
  },
end


--#check (F (λ b : bool, 10) 10)
--none

-- nat.succ (G nat.zero [(fun x : nat, x+2) 13] tt)
-- nat -> list nat -> bool -> nat


def elem : nat -> list nat -> bool
  | x [] := ff
  | x [y] := x = y
  | x (y :: L) := elem x L 

example: elem 3 [] = ff := begin refl, end 
example: elem 3 [1] = ff := begin refl, end 
example: elem 3 [1,2] = ff := begin refl, end 
example: elem 3 [1,2,3] = tt := begin refl, end 
example: elem 3 [1,3,2,3] = tt := begin refl, end


theorem Q42 : ∀ x : ℕ, elem x [] = ff 
:= begin
  sorry,
end

theorem Q43 : ∀ x y : ℕ, ∀ L : list ℕ, elem x L → elem x (y :: L) 
:= begin
  sorry,
end

def app : list nat -> list nat -> list nat 
  | [] L := L 
  | (a :: L1) L2 := a :: (app L1 L2)

theorem elemapp: forall x : nat, forall L1 L2 : list nat, 
  elem x (app L1 L2) = elem x L1 ∨ elem x L2 
:= begin sorry end

def duplicateLast :list ℕ → list ℕ
  | [] := []
  | [y] := app [y] [y]
  | (y :: L) := app [y] (duplicateLast L)

example : duplicateLast [ ] = [] := begin refl end

example : duplicateLast [13] = [13, 13] := begin refl end

example : duplicateLast [1, 2, 3] = [1, 2, 3, 3] := begin refl end

def lastElement : list ℕ → ℕ
  | [] := 0
  | [x] := x
  | (x :: L) := lastElement L

example : lastElement [] = 0 := begin refl end

example : lastElement [1] = 1 := begin refl end

example : lastElement [1, 2] = 2 := begin refl end


theorem Q65: ∀ L : list ℕ, duplicateLast L = app L [(lastElement L)]
:= begin
  sorry,
end