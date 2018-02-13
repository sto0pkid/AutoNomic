#so this is some total basics stoop wrote, i think just copying agda stdlib for the most part
#ugh howto ne
--all i know of emacs is, f10 is menu. a good one to know if you only know one xD C-x-s is save btw:)

```
module lc-essentials where

open import Agda.Primitive

data Nat : Set where
 z : Nat
 suc : Nat -> Nat
-- so, refresher on peano numbers? that's church encoding? i think its peano numbers
-- might be both hehe like... cna't recall off top of head.
-- λs.λz.s (s (s z)) == tthree
-- yeah its that principle
-- okay, i tohhin!k i yeah I think I get it now. peano numbers encode the meaning behind numbers
-- it applies a function n times. so apply suc n times to z you get nat n
-- yeah unary 
-- oh god

data LambdaVar : Set where
 V : Nat -> LambdaVar

data LambdaTerm : Set where
 Var : LambdaVar -> LambdaTerm
 App : LambdaTerm -> LambdaTerm -> LambdaTerm
 Abs : LambdaVar -> LambdaTerm -> LambdaTerm

-- Abs = abstraction - lambda definition. k

data Pair (A B : Set) : Set where
 _,_ : A -> B -> Pair A B

first : {A B : Set} -> Pair A B -> A
first (a , _ ) = a

second : {A B : Set} -> Pair A B -> B
second (_ , b) = b

data List (A : Set) : Set where
 [] : List A
 _::_ : A -> List A -> List A
```
_::_ = ?
so what were you wondering again? -back-

There's not really a specific thing I was wondering. Just trying to learn more in general.
Let me poke through this file real quick and see what I do and don't understand.

i think this is a data declaration, might explain the :
wait no, this is a definition for an operator. I think. an `infix` operator
yeah...dunno
maybe its just a declaration of the type tho?
well _::_ is a pattern, everything after that and the ':' is the type.  ye
_ is a placeholder. an infix can be put in the middle of it's arguments instead of
exclusively before args. thus the two placeholder '_'s. that's my interpretation at least.
i agree wrt placeholder _'s andthis being an infix operator
shall we jump into emacs and see if it compiles? yeah. one sec though
```
data Bool : Set₀ where
 true : Bool
 false : Bool

-- if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if_then_else_ : { i : Level} -> {A : Set i} -> Bool -> A -> A -> A 
if true then x else y = x
if false then x else y = y

_and_ : Bool -> Bool -> Bool
true and true = true
true and false = false
false and true = false
false and false = false

_or_ : Bool -> Bool -> Bool
true or true = true
true or false = false
false or true = false
false or false = false

Nat-eq : Nat -> Nat -> Bool
Nat-eq z z = true
Nat-eq (suc x) z = false
Nat-eq z (suc y) = false
Nat-eq (suc x) (suc y) = Nat-eq x y


LambdaVar-eq : LambdaVar -> LambdaVar -> Bool
LambdaVar-eq (V x) (V y) = Nat-eq x y
--this is starting to get confusing about here vvvvv

--item in list
-- so, takes list of lambdavars, a lambdavar we're looking for, and returns bool
list-in : List LambdaVar -> LambdaVar -> Bool
-- for empty list, the answer is false
list-in [] v = false
-- patern match the list for head and tail, if the head equals the sought element, return true
-- otherwise recurse with the tail. but where will it return false if it's not found?
-- it will just recurse until the empty tail. oh tru
-- okay cool.
list-in (l :: ls) v = if (LambdaVar-eq l v) then true else (list-in ls v)

list-union : List LambdaVar -> List LambdaVar -> List LambdaVar
list-union [] rs = rs
list-union (l :: ls) rs = if (list-in rs l) then (list-union ls rs) else (l :: (list-union ls rs))

remove_from_ : LambdaVar -> List LambdaVar -> List LambdaVar
remove x from [] = []
remove x from (l :: ls) = if (LambdaVar-eq x l) then (remove x from ls) else (l :: (remove x from ls))

-- FV =?
-- free variables. c ool.(in a lambda expression)
-- free vars are instances of the parameter in the body. correct?
-- i dont understand the question. this builds up a list of free vars in the r variable
-- ah as in in lc, free vars are those that arent bound/captured somewhere above where they appear
-- bound by being a parameter to a lambda.
-- okay. this has confused me in the past. So what you're syaing is a free var is, for example, what?? haha
-- like, in the expression λx.x, there are no free vars
-- but λx.y, y is free. got it.
-- stoop wants us to change a line real quick.
-- hotkey: C-c-l is compile in agda-mode.. apparently not active here? there.
-- i think thats, like, C-c C-l, yeah I just string it together because lazy
--i see, i think it works then
--yeah the lag just caused me to not notice the coloring blip ic
FV-helper : LambdaTerm -> List LambdaVar -> List LambdaVar
FV-helper (Var x) r = x :: r
FV-helper (App t s) r = list-union (FV-helper t r) (FV-helper s r)
-- isn't the union unecessary here?
-- they are the same (FV-helper t r). that makes more sense tome.definitely, good catch
FV-helper (Abs x e) r = remove x from (FV-helper e r)

FV : LambdaTerm -> List LambdaVar
FV t = FV-helper t []

-- gte = ? greater than
-- what if for (suc x) gte z = true, z = suc ?)
-- z is the zero in Nat

_gte_ : Nat -> Nat -> Bool
z gte z = true
(suc x) gte z = true
z gte (suc y) = false
(suc x) gte (suc y) = x gte y

-- why do we need to wrap the arguments wiht suc?
max : Nat -> Nat -> Nat
max z z = z
max z (suc y) = (suc y)
max (suc x) z = (suc x)
max (suc x) (suc y) = suc (max x y) -- i think maybe this should be = (suc (max x y)). something about it
-- is seeming strange indeed. would like to see it used
-- well, we can try. make it so~ gonna start a cup of joe real quick alright
-- if i can google how to print something in agda
-- it would be cool if there was like a, connected terminal is trying to input,
{-
alert, and waits like one second before allowing input. its not that bad, you getused to it. It's true. Like I was saying in irc i've done this before with friends,
yeah true
lol
 right!
 its supposed to be quite a beefy vps, but itwas maybe too cheap i guess..
 kind of think that I could just host. Well, if you feel like it. or at least help go in on
 a nicer vps. I'm open to it though and this computer is always on. I'd have to talk to the others
 on my network and make sure that's okay though. discussion for another time though I think.
 yeanh. what kind of computer, at work? home. Decent cpu desktop comp. I have roomates that are techies.
 thus the need to ask.
 i guess i can at least go poke at the vps control panel, maybe i find something. worth a shot.
-}
maxVar : LambdaTerm -> Nat
maxVar (Var (V n)) = n
maxVar (App t s) = if ((maxVar t) gte (maxVar s)) then (maxVar t) else (maxVar s)
maxVar (Abs (V n) e) = if (n gte (maxVar e)) then n else (maxVar e)

freshVar : LambdaTerm -> LambdaVar
freshVar t = V (suc (maxVar t))

data True : Set₀ where
 unit : True

data False : Set₀ where
omega : ∀ {i} -> {A : Set i} -> False -> A
omega ()

data _==_ {i} {A : Set i} (x : A) : A -> Set i where
 refl : x == x

==-refl : ∀ {i} {A : Set i} (x : A) -> x == x
==-refl x = refl

==-sym : ∀ {i} {A : Set i} {x y : A} -> x == y -> y == x
==-sym {i} {A} {x} {.x} refl = refl

==-trans : ∀ {i} {A : Set i} {x y z : A} -> x == y -> y == z -> x == z
==-trans {i} {A} {x} {.x} {.x} refl refl = refl

¬ : ∀ {i} -> (A : Set i) -> Set i
¬ A = A -> False

_≠_ : ∀ {i} {A : Set i} -> (x y : A) -> Set i
x ≠ y = ¬ (x == y)

≠-antirefl : ∀ {i} {A : Set i} (x : A) -> ¬ (x ≠ x)
≠-antirefl {i} {A} x [x≠x] = [x≠x] (==-refl x)

≠-sym : ∀ {i} {A : Set i} {x y : A} -> x ≠ y -> y ≠ x
≠-sym {i} {A} {x} {y} [x≠y] [y==x] = [x≠y] (==-sym [y==x])



A==B-implies-A-implies-B : ∀ {i} {A B : Set i} -> A == B -> A -> B
A==B-implies-A-implies-B {i} {A} {.A} refl a = a


True≠False : True ≠ False
True≠False [True==False] = A==B-implies-A-implies-B [True==False] unit

BoolToSet : Bool -> Set₀
BoolToSet true = True
BoolToSet false = False

cong : ∀ {i j} {A : Set i} {B : Set j} -> (f : A -> B) -> (x y : A) -> x == y -> (f x) == (f y)
cong f x .x refl = refl

true≠false : true ≠ false
true≠false [true==false] = contradiction
 where
  [True==False] : True == False
  [True==False] = cong BoolToSet true false [true==false]

  contradiction : False
  contradiction = True≠False [True==False]


isZero : Nat -> Bool
isZero z = true
isZero (suc n) = false

zero≠sucn : (n : Nat) -> z ≠ (suc n)
zero≠sucn n [z==sucn] = true≠false (cong isZero z (suc n) [z==sucn])

-- height is measured in intervals (graph/tree edges, or, tiers of these, anyway) rather
-- than points (nodes), just like on a ruler
height : LambdaTerm -> Nat
height (Var x) = z
height (App t s) = suc (max (height t) (height s))
height (Abs x e) = suc (height e)


pred : Nat -> Nat
pred z = z
pred (suc n) = n
```
