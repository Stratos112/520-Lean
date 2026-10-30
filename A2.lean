-- Sky Vercauteren
-- CS 520
-- Assignment 2





-- fastPow for Question 1
def fastPow (b n : Nat) : Nat :=
  if n = 0 then 1
  else if n % 2 == 0 then
    let half := fastPow b (n / 2)
    half * half
  else
    b * fastPow b (n - 1)
termination_by n
decreasing_by
  · omega
  · omega

#eval fastPow 2 10   -- expect 1024
#eval fastPow 3 5    -- expect 243
#eval fastPow 7 0    -- expect 1


-- ## Q1:
-- A.)
-- The GCD demonstration in class as I recall only had a single recursive path.
-- e.g. it either terminates or it continues to recurse along the same path.
-- Conversley, this fastPow algorithm contains two different recursive paths wherein
-- the decision tree could follow either of two branches. As such it makes sense that
-- Lean can not assume either case is true, and needs reassurance of both of them.

--B.)
#check fastPow.induct
-- case 1 is when n = 0
-- case 2 is n is even
-- case 3 is n is odd

--C.)
#check fastPow.eq_def
#check if_neg
#check Nat.pow_two
#check congr
#check beq_iff_eq

theorem fastPow_correct (b n : Nat) : fastPow b n = b ^ n := by
  induction n using fastPow.induct (b := b) with
  | case1 =>
    rw [fastPow.eq_def] -- I feel like this should be implicit.
    rw [Nat.pow_zero] -- this is for my own sanity lol.
    simp

-- D.)
  | case2 x hx0 heven ih =>
    rw [fastPow.eq_def]
    rw [if_neg hx0, heven]
    simp
    rw [ih]
    rw [← Nat.pow_add]
    rw [← Nat.mul_two]
    --grind
    -- wait I can do this
    rw [Nat.div_mul_cancel]
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [beq_iff_eq] at heven -- Ok I had to google this one.
    -- I just needed to get (2 % x == 0) = true  .. to be .. 2 % x = 0
    exact heven

-- E.)
  | case3 x hx0 hodd ih =>
    rw [fastPow.eq_def]
    rw [if_neg hx0]
    rw [Bool.not_eq_true] at hodd
    rw [hodd]
    simp
    rw [ih]
    rw [← Nat.pow_add_one']
    rw [Nat.sub_add_cancel] -- same thing as above. I could spend time showing that 1 divides x but meh.
    grind




-- gcd for Question 2
def gcd (a b : Nat) : Nat :=
  if b = 0 then a
  else gcd b (a % b)
termination_by b
decreasing_by
  apply Nat.mod_lt
  omega

theorem dvd_add_mod (d a b : Nat) (hb : d ∣ b) (hr : d ∣ a % b) : d ∣ a := by
  obtain ⟨c, hc⟩ := hb
  have hmul : d ∣ b * (a / b) := ⟨c * (a / b), by rw [hc, Nat.mul_assoc]⟩
  have heq : a % b + b * (a / b) = a := Nat.mod_add_div a b
  rw [← heq]
  exact Nat.dvd_add hr hmul

theorem gcd_dvd (a b : Nat) : gcd a b ∣ a ∧ gcd a b ∣ b := by
  induction a, b using gcd.induct with
  | case1 a =>
    rw [gcd.eq_def]
    simp
  | case2 a b hb ih =>
    rw [gcd.eq_def, if_neg hb]
    obtain ⟨ih1, ih2⟩ := ih
    exact ⟨dvd_add_mod _ a b ih1 ih2, ih1⟩

theorem gcd_dvd_left (a b : Nat) : gcd a b ∣ a := (gcd_dvd a b).1
theorem gcd_dvd_right (a b : Nat) : gcd a b ∣ b := (gcd_dvd a b).2


-- 2.)
#check Nat.dvd_mod_iff

--B.)
/--

d ∣ b → (d ∣ a % b ↔︎ d ∣ a)

This lemma is saying "If d divides b (evenly) then with some other
natural number 'a' then d also divides the remainder of a divided by b, Iff,
d also divides a". For example, if 4 divides 8, then 4 also divides
32 mod 8 if and only if 8 also (evenly) divides 32. If we tried to use 30
instead, then we could show that neither 4 divides 30 mod 8 (evenly), nor
that 8 divides 30 evenly.

In lecture we saw that the set of divisors of a with b and b with
a mod b is the same set of divisors. I think the slides refer to this
as Euclidian Algorithm? To illustrate an example again, the commomn
divisors of 30 and 8 are the same as the divisors of 8 and (30 mod 8).
The set of common divisors of 8 and 30 is {1,2}, 30 mod 8 is 2, which
shares divisors {1,2} with both 8 and 30.

In my mind this lemma is saying "a thing either divides another thing
evenly, or it doesnt. If it does then the remainder is 0, and 0 = 0 qed,
but if it doesnt, then all the things that divide the remainder must also
divide both of the dividends independently." As per our example, 2 (with
divisors {1,2}) has the same divisor relationship with 8 (common divisors
{1,2}), as it does with 30 (common divisors {1,2}).

--/

--A.) and C.)
theorem dvd_gcd (a b d : Nat) (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  induction a, b using gcd.induct with
  | case1 a =>
      rw [gcd.eq_def]
      simp
      exact ha
  | case2 a b hb' ih =>
    rw [gcd.eq_def]
    rw [← ne_eq] at hb'
    rw [if_neg]
    apply ih -- This is the line that I got stuck on though. It's hard to conceptualize the IH as 3 parts.
    . exact hb
    . rw [Nat.dvd_mod_iff hb]
      exact ha
    . exact hb'

-- Not sure if this is what you had in mind!
