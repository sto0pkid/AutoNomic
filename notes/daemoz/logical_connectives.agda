module logical_connectives where

open import Agda.Primitive

data Bool : Set where
 true : Bool
 false : Bool

-- you're on the write track
-- and i'm on the wrong track with grammar lol

-- _and_ is not a data-type it's just a regular function so no 'data'
-- the cartesion product one is a type though? indeed, or, type-constructor anyway
_and_ : Bool → Bool → Bool
true and true = true
true and false = false
false and true = false
false and false = false

-- just trying to think of a clean way to do it is all
-- neato nice
_or_ : Bool → Bool → Bool
_or_ true = λ x → true
_or_ false = λ x → x



-- can be simplified some:
_and'_ : Bool → Bool → Bool
_and'_ true = λ x → x
_and'_ false = λ x → false

-- when you pattern-match on an argument you need to cover all cases
-- in this case true and false so we have a line for each case
-- in the first function _and_ we pattern-matched on both inputs and
-- got 4 cases, this function _and'_ we pattern match on the first inputs,
-- and then return the function that's gonna operate on the second input
-- this one is more elegant

_and''_ : Bool → Bool → Bool
true and'' true = true
_ and'' _ = false

-- hrm i can't tell if that worked or not XD
-- so on an example I was pretty sure was correct it did this white
-- highlighting thing too, idk what it means but everything worked fine.
-- yea works
-- this one's maybe "most" elegant, probably the shortest version
-- you could write, but, that's sort of a matter of preference i guess
-- they all do exactly the same thing, pretty much all the way down

data Dog : Set where
 fido : Dog

data Cat : Set where
 oliver : Cat

data DogORCat : Set where
 dog : Dog → DogORCat -- so this one says that if you have a Dog, then you have a DogORCat 
 cat : Cat → DogORCat -- and this one says that if you have a Cat, then you have a DogORCat
 -- any closer? very close, definitely got the right idea
{-
try filling this one out and then generalize to A ∨ B
-}

data _∨_ (A : Set) (B : Set) : Set where
 inl : A → A ∨ B
 inr : B → A ∨ B
-- hehe there you go
-- usually they call them inl and inr or left/right but thing1 and thing2 works :)
-- also later things can be put under modules and namespaces and such so things don't get clobbered

-- so to construct this datatype I would say: "thing1 x"? where x is a Cat, if the type is specified to Cat ∨ {something}

myCat : Cat ∨ Dog
myCat = inl oliver -- whoa okay

myDog : Cat ∨ Dog
myDog = inr fido


-- so and, or and bool stuff is done. What about expressing the empty and singleton sets?

data True : Set where
 unit : True

-- but..

data False : Set where
-- just don't put anything?
-- right
-- it's empty :)
-- cool!
-- idk whether it has principle of explosion built-in if you don't put anything else but
-- we'll leave that for later

data FalseDefinitelyWithExplosion : Set where

omega : ∀ {i} {A : Set i} → FalseDefinitelyWithExplosion → A
omega () 
-- ah now i remember more about why this is defined this way, but, yea we'll leave that for later :)
-- sounds good! Gonna go for a bit, thanks for getting me up-to-speed on these. Sure thing
-- now we're pretty close to actually modeling stuff and proving propositions, catch ya later :)

-- "dogs ∨ cats" is a set, if "dogs" is a set and "cats" is a set
{-
data _∨_ (A : Set) (B : Set) : Set where -- that's what this
 A ∨ _ : B → A ∨ B -- ? i sort of see what you're going for, want to write out
-}
 -- these object-constructors are you specify what it means to provide an object
 -- of type "dog ∨ cat"
 -- your thought process behind this and i can help you work that into correct syntax? sure
 {-
How can I  have a set, that contains either a set, or another set, if the type-class(?)
requires two inputs anyway then no matter what I'll have to have two sets. right?
well, you have two *sets*, but to provide a proof you only need an object from either one
like if i say "a dog OR a cat", i've got two sets in question, "dogs" and "cats", but
to provide a proof that i have "a dog OR a cat", i only need to provide either a dog
or a cat, not both

 -}
-- confused about in what way it will be different from ∧. also brb
-- well, for A ∧ B we need both an A and a B, but for A ∨ B, just an A should suffice
-- alternatively, just a B should suffice as well
-- can I construct one of your "A ∨ B"s without having both? :)
-- hint: you can have more than one constructor

-- so this data-type can only be constructed if you have an A and a B, and that encodes the meaning?
-- so, we can break this up into two parts, there's a "type-constructor" part and an "object constructor"
-- part. usually when we say the "constructors" we mean the object constructors
data _∧_ (A : Set) (B : Set) : Set where -- type constructor / type-formation-rules part
--       takes a set A, and another set B, and returns the set A ∧ B, whose objects are defined by
--       the obect constructor below
{-
the type-constructor part above defines _∧_ as a function taking two Sets/Propositions and returing
another Set/Proposition
so, you need two Sets in order to construct an "_∧_ type"
in other words, _∧_ : Set → Set → Set

-}
 _,_ : A {-takes an object of type A-} → B {- and an object of type B-} → A ∧ B {- and returns an object of type A ∧ B -}
 -- object constructor / "introduction rules" part

-- so the objects of A∧B can only be constructed with pairs (a , b) where a is an A and b is a B, and
-- that (along with the elimination and computation rules that are automatically derived from this
-- definition) defines the meaning of the type A∧B, yes

-- the constructor takes an A, and a B, and returns an A ∧ B
-- an A and a B is what you should need in order to derive an A ∧ B
-- when you write your constuctors you think about what's gonna be the
-- evidence that witnesses the truth of the proposition defined by your datatype


-- so, this is sort of an encoding of what the "elimination" rules for _∧_ are,
-- the elimination rules specify what you can derive from A ∧ B
-- these aren't actually the elimination rules though, like I said, those are
-- automatically derived from your data-type definition, and basically provide
-- the scheme for pattern-matching on objects of that type
first : {A B : Set} → A ∧ B → A
first (a , _) = a

second : {A B : Set} → A ∧ B → B
second (_ , b) = b


-- you don't really "see" the computation rules much until you start actually
-- computing with the things and evaluating functions, either at type-check
-- (when type-checking dependent-types) or during run-time when you're actually
-- running functions

-- C-c C-n first (true , false) <ENTER>

-- i was confused at the difference between the elimination and computation rules
-- for a while, since they both just seem to be describing how to make functions
-- out of the type, but basically the elimination rules tell you whether or not
-- these functions should *typecheck* and the computation rules tell you how
-- to then normalize the terms, i.e. the rules stating that first (true , false)
-- evaluates to true

-- following so far? if so i'll hand it back over to you to try _or_ and _∨_
-- I think I'm following. The elim/comp rules thing is something I'll work on later.
-- I'll try to make the boolean or and the set or now.




-- yo
-- yo
