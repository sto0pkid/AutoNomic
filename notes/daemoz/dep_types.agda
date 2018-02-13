open import Agda.Primitive


-- Of course it's not this easy xD
-- ok so
-- Exists A : Type, Exists x : A, Forall y : A , x == y

-- Am I missing some agda boilerplate?
-- a bit:

{-
∃ = \ex
∀ = \all
oh wait you know all that already
-}


-- :)
-- so, pretend you don't see any of the i's and j's done! xD

-- so you're familiar with parameterized types? vector<int> ye

-- so we've got some parameters here:
-- Exists a ∈ A, such that P(a)
-- take the domain A as the first parameter
-- take this function P as the second parameter
-- P is a function that takes objects in type A and
-- returns propositions about them.
-- so these multiple statement seperated by spaces but before the ':'
-- these all add together to be.. ? the type?
-- they're the parameters to the type-constructor Exists
-- so, Exists is like a function that takes a set A, and
-- the function P : A -> Set, and returns a Set (proposition)
-- I did I guess xD
-- ok so i guess i'll explain the letters while we're at it
-- ok so you know russell's paradox?
-- what's the set of all sets that don't contain themselves?
-- a paradoxical one that's for sure
-- I don't, lets stick to ignoring them for now hahaha
-- well, basically the moral of the story is that the sets
-- get split out into an infinite hierarchy so you have
-- Set : Set 1
-- Set 1 : Set 2
-- etc...
-- and then you can make these "level-polymorphic" functions
-- by quantifying over levels

-- Set (i ⊔ j) == return type? right
-- ⊔ is ? max == lub == least-upper-bound. hrm..
-- why they couldn't just say 'max', idk,
-- so, A has type Set i, and P has type A -> Set j
-- so Exists A P will be in the bigger of the two sets
-- bigger = more members?
-- higher level in the
-- wait i thought i told you to forget the letters
-- you did! but you brought them back in!
-- so now my Exists will work at any Set-levels
-- brackets mean inference?
-- right implicit arguments, you don't need to pass them if it
-- can infer
-- so Set (i ⊔ j) would mean the set that has the highest level?
-- of the two. right yaaaas
data Exists {i} {j} (A : Set i) (P : A -> Set j) : Set (i ⊔ j) where
 _,_ : (a : A) -> P a -> Exists A P
-- so then the constructor
-- takes a value a : A, and a proof that P(a), and says, "yep, that's a proof of Exists A P"
-- or in other words: ∃ a ∈ A , P(a)


-- so basically these are elements I needed to make the singleton type work, that I misinterpretted
-- to be part of agdas stdlib, you can find these things in the stdlibs i just usually
-- write them up myself /  have my own nonstdlibs
-- gotcha. but the analog to what I was trying to write at the top of this file is the singleton type?
syntax Exists A (λ x → e) = ∃ x ∈ A , e
-- so when you give the syntax on the right, it will rearrange and
-- interpret it as what's on the left.
-- -∃ a ∈ A , P(a)

-- ∃ x ∈ A , P(x)   -- rearrange --> Exists A (λ x → P(x))
-- what does the syntax operator do?
-- let's you use alternative syntax, oh, like a typedef or osmething
-- right maybe even more like a macro i'm not sure how it works on the internals. sure.

data _==_ {i} {A : Set i} (x : A) : A -> Set where
 refl : x == x

singletons : Set₁
singletons = ∃ A ∈ Set , (∃ x ∈ A , ((y : A) → x == y)) -- commas are like adding additonal restraints?
-- comma is the constructor for Exists
-- _,_ : ... :) oh word. okay that's neat. exists proves(?) that A is an element of the set provided?
-- exists x ∈ A , P (x) proves ... exists x ∈ A , P (x) :)
-- proves that the proposition P holds for the element x
-- you could just prove P(x) <--

-- I think my brain is just not wanting to do this right now. I have some notes now though to use
-- when I go back and study this later. I think I'm at a limit for tonight though.
-- no problem, seems like you're already catching on pretty well so yea go relax and let it
-- absorb or something :)

-- Haha, that's the strat! THanks for going over all of this (inc irc chat we had). yea whenever
-- Alright, talk to you later~cya:)

-- but this packages it up so you have P(x) along with the object x that it's a proof for
-- along with the type that relates them together
-- plus you can quantify over these
--
-- (s : singletons) -> ... 
-- ∃ s ∈ singletons , ...


-- you understand this def? yes.
data True : Set where
 unit : True




_is-singleton : Set → Set
A is-singleton = ∃ x ∈ A , ((y : A) → x == y)

True-is-singleton' : (y : True) → unit == y
True-is-singleton' unit = refl

True-is-singleton : True is-singleton
True-is-singleton = (unit , True-is-singleton')

-- there you go
-- whoa, that was a lot more than I was expecting it to be,
-- as you can tell by my 'attempt' xP
-- A LOT of this I do not understand but I think that means I
-- need to go through that learn-you-an-agda tutorial because
-- I'm clearly missing some basics of the language.
-- well let's learn you an agda real quick:

