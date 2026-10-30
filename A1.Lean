-- Sky Vercauteren
-- CS 520
-- Assignment 1



-- Declare a predicate "Even" which takes a single natural number n as input and outputs a proposition (type Prop).
-- It is useful to recall that propositions are things that are true or false and think of predicates as functions which take some input(s) and give back a proposition.
def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- Looking at the definition, a number n is even if there exists some (natural number) k such that n = 2 * k.
example : Even 4 := ⟨2, rfl⟩
example : Even 0 := ⟨0, rfl⟩

theorem even_add_even (a b : Nat) (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨j, hj⟩ := ha
  obtain ⟨k, hk⟩ := hb

  --trace_state

  -- note, #check didnt work for me, maybe its a top level execution? I looked up other ways to get debug information out of curiosity and found trace_state
  -- The variables a, b, j, and k are all defined as Nat numbers per the argument definition either in even_add_even or the Even proposition.
  -- However variables hj and hk are 'Even propositions' meaning they have the type 'a = 2 * k'. We are essentially saying:
  -- "we can show that a and b uphold the hypothesis of being even by 'obtaining' some values j and k that can each be multiplied by 2 to get a and b respectively".

  refine ⟨j + k, ?_⟩
  -- is this thed correct keyword? Not sure the instructions where clear about how to provide a witness?

  omega
  -- While I'm not exactly sure the steps that omega took here, I would think that it would start by proving the distributive property.
  -- Once it has shown that 2(a + b) = 2a + 2b, it can then use the "Even" predicate we defined above to complete the proof via rfl.

def Odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

example : Odd 1 := ⟨0, rfl⟩
example : Odd 5 := ⟨2, rfl⟩

theorem even_cube_even (a : Nat) (ha : Even a) : Even (a * a * a) := by
  obtain ⟨j, hj⟩ := ha
  rw [hj]
  rw [Nat.mul_assoc (2 * j)]
  rw [Nat.mul_assoc]
  exact ⟨(j * (2 * j * (2 * j))), rfl⟩

  -- it feels silly to me that it didnt know the assosciativity? or the exact. Im still not sure im understanding how to use lean in this way.

-- this is a helper for Both of the next two questions/
theorem even_one_more (a : Nat) (ha : Even a) : Odd (a + 1) := by
  obtain⟨j,hj⟩ := ha
  rw [hj]
  exact ⟨j, rfl⟩

  -- theorem odd_cube_odd (a : Nat) (ha : Odd a) : Odd (a * a * a) := by
--   obtain ⟨j, hj⟩ := ha
--   -- (2j +1) (2j + 1) (2j +1)
--   -- = (4j^2 + 4j + 1) (2j +1)
--   -- = 8j^3 + 12j^2 +6j + 1 .. but we want 2x + 1 so keep the 1 and divide the rest by 2
--   -- = 4j^3 + 6j^2 + 3j is our x
--   let x := 4 * j * j * j + 6 * j * j  + 3 * j
--   refine ⟨x, ?_⟩
--   rw [hj]
--   -- have ho := even_one_more x .. lol and I dont even need it. sigh.
--   have eq : (2 * j  + 1 ) * (2 * j  + 1) * ( 2 * j + 1) = 2 * x + 1 := by
--     rw [Nat.add_mul]
--     rw [Nat.mul_assoc]
--     --rw [Nat.add_assoc]
--     rw [Nat.add_mul] -- sigh. god wait this is going to take forever.
--   omega -- didnt work
-- have hz : Odd ( 2 * j + 1) := ⟨j, rfl⟩
    -- have hi' : (2 * j + 1) * (2 * j + 1) * (2 * j + 1) = 2 * k := by grind
    -- have hi : k = (4 * j * j * j) + (6 * j * j) + (3 * j) := by grind
    -- rw [hi]
    -- have hiz : Odd (2 * (4 * j * j * j + 6 * j * j + 3 * j)) = Odd ( 2 * j + 1) := by grind
    -- rw [hiz]


-- *** Coming back after completion to say that something like the above would be trivial with grind! any of these ideas!


theorem odd_one_more (a : Nat) (ha : Odd a) : Even (a + 1) := by
  obtain⟨j,hj⟩ := ha
  rw [hj]
  rw [Nat.add_assoc]
  rw [← Nat.mul_add_one]
  exact ⟨(j + 1), rfl⟩


-- ok wait, if I do this first, I can use contradiction to prove the other one?
theorem all_nat_even_or_odd (a : Nat) : Even a ∨ Odd a := by
  induction a with
  | zero =>
    left
    exact ⟨0, rfl⟩
  | succ n ih =>
    cases ih with -- ok I had to look up cases based on the error.
    -- so in the induction step we want to say that n could be even or odd.
    -- (( trivial math/review question: why can't I show sducc on the base case again? why do we assume an arbitrary n?))
    | inl hl => -- so lets assume n is even.
      right -- omg this threw me so hard. Ok so even though we assumed n is even, we still need to tell lean to change the goal.
      -- if n is even then n+ 1 must be odd
      exact even_one_more n hl
    | inr hr =>
      left -- as above, assuming n is odd, we need to show its + 1 is even
      -- I paused here and definined odd_one_more as the complement of even_one_more
      exact odd_one_more n hr

--cool so now I should be able to use this and contradiction to show odd_cube_odd
theorem odd_cube_odd (a : Nat) (ha : Odd a) : Odd (a * a * a) := by
  apply Classical.byContradiction -- thanks Ewen, this is the part I was missing.
  intro hneg -- its not recursive though, so just a single variable.
  cases all_nat_even_or_odd (a * a * a) with
  | inr h0 => exact hneg h0 -- its odd lol
  | inl h1 =>
    obtain ⟨j, hj⟩ := ha -- unpack j as 2 * j + 1
    obtain ⟨k, hk⟩ := h1 -- unpack as even
    -- I guess we still have to show lean by hand that it cant be both.
    -- theres got to be a way here to use one or some of the following:
    --    - even_cube_even
    --    - even_one_more
    --    - odd_one_more
    --    - or neither_even_nore_odd false
    -- but alas, I guess grind can figure out they cant be the same anyway.
    have hbad : (2 * j + 1) * (2 * j + 1) * (2 * j + 1) = 2 * k := by grind
    grind --silly to grind twice.
