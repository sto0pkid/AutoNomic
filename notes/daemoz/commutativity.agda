open import Agda.Primitive

data False : Set where
-- no constructors; False is an empty set

-- one eliminator though:
-- principle of explosion; False proves everything
omega : ∀ {i} {A : Set i} → False → A
omega () -- Haskell compilation stuff to make this have a proof, since... black magic, got it
         -- well, basically it's supposed to be an inference rule, but they're basically
         -- encoding it as a theorem and then forcing it to have a proof so that it behaves
         -- like an inference rule
         -- I guess it's just way different from all the other rules which follow the same
         -- basic formula so they kinda "black magick'd" it


data True : Set where
 unit : True

-- True → True
-- False → False
-- {A : Set} → A → A
-- False → True
-- (True → False) → False
-- _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C)
-- mp : {A B : Set} → A → (A → B) → B
-- haha ty

True→True : True → True
True→True x = x -- is this sufficient? Agda certainly thinks so

False→False : False → False
False→False x = x

Any→Any : {A : Set} → A → A
Any→Any x = x -- hahhaah

False→True : False → True
-- erm, is this PoE stuff? it can be, but there's also a proof of True that you can just provide
False→True _ = unit

-- like right about here, the names haha
ImpliesFalse→False : (True → False) → False
ImpliesFalse→False x = x unit -- wohooo nice :)
-- so what's the type of A here? no.. (True → False)
-- can you get a False out of that? by calling it? : )
-- if you have a function of type A → B, what do you need to call it on
-- in order to get a B?

-- now you have function application :D
-- jk you already had that, it's the built-in elimination rule for _→_
mp : {A B : Set} → A → (A → B) → B
mp a a2b = a2b a

-- cool now you have function composition :)
-- stoop logic is so pretty haha, lol just wait :D
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C) -- what lol i found it
_∘_ b2c a2b = λ a → b2c (a2b a) -- you're on the right track
-- but b2c is a function of type B → C, it needs a B as input and you're passing
-- it an A → B
-- warmer, first remember that it left-associates not right-associates
-- so a b c is (a b) c not a (b c)
-- everything you have there is right, you're just missing some other things
-- now where's this A coming from?
-- what's the type of "b2c (a2b a)", assuming a : A ? C
-- what do you need to be returning though? (if all you've taken so far is (!!!! :)
data Bool : Set where
 true : Bool
 false : Bool

_and_ : Bool → Bool → Bool
_and_ true = λ x → x
_and_ false =  λ x → false

_or_ : Bool → Bool → Bool
_or_ true = λ x → true
_or_ false = λ x → x

_==_ : Bool → Bool → Bool
_==_ true true = true
_==_ false false = true
_==_ _ _ = false
-- like this; technically the data way will work too but you'll find that it's unnecessary/redundant
-- since you're not introducing any new connectives/relations you're just using existing logic
-- ah so needless names
proof-comm-of-and : Bool → Bool → Bool
proof-comm-of-and x y = (x and y) == (y and x) -- wait is this naive?
-- technically this not a proof of commutativity of OR it's just a function that computes some value from two Bools
-- but i see what you're going for :)
-- so for it to be a proof it has to be express through the type system alone?
-- right, the type encodes the proposition being proved, all you've proven here is you've got a binary operation
-- on Bools
-- can you show me how to encode it as a type?

-- let's start with symmetry of _∨_, it's a bit easier and will get you warmed up a bit
-- before i show you identity types
data _∨_ (A : Set) (B : Set) : Set where
 inl : A → A ∨ B
 inr : B → A ∨ B

data _∧_ (A : Set) (B : Set) : Set where
 _,_ : A → B → A ∧ B

-- getting warmer
-- it's not like haskell it doesn't automatically infer that you have a type-variable there
comm-∨-p : {-take them as parameters: -} {A B : Set} → A ∨ B → B ∨ A -- you're on the right track
comm-∨-p (inl A) = (inr A)
comm-∨-p (inr A) = (inl A)
-- word hell yeah

comm-∧-p : {A B : Set} → A ∧ B → B ∧ A
comm-∧-p (A , B) = B , A -- aww hell yeah :D

-- how about A ∧ B → A ∨ B and then we'll try True/False stuff.
-- I don't understand the logical connection between A ∧ B → A ∨ B.
-- does having both a dog and a cat prove that you have either a cat or a dog? ahh..
-- I think I'm just always ready to be hearing about some other known axiom of logic that I forget to use common sense xD

somefancyname-∧-to-∨-p : {A B : Set} → A ∧ B → A ∨ B
somefancyname-∧-to-∨-p (A , B) = inl A -- hell yea. I don't understand why that one case is sufficient. I feel
-- like I need " ... = inl B" do you? Agda's not throwing any errors :P
-- that's true but what if it's a different B? like er... well I guess it has all the type information it needs
-- from the constructor. right
-- so if you're thinking, what if some later program down the road is using this and needs for you to have
-- given the B instead? it can't, because it must be accepting an object of type A ∨ B and must therefore
-- be fine accepting either one. that's true. if it needs just a B, it needs to specify that it takes just an
-- B as its input, and if its specifying A ∨ B, then it gets what it gets :)
-- but, you can prove A ∧ B → A, and A ∧ B → B
someproof : {A B : Set} → A ∧ B → A
someproof (A , _) = A


someproof' : {A B : Set} → A ∧ B → B
someproof' (_ , B) = B -- these are kind of addicting yes :D
-- now you know why AutoNomic dev takes so long XD must prove all the things!

data Dog : Set where
 fido : Dog

data Cat : Set where
 oliver : Cat

data Dog∨Cat : Set where
 dog : Dog → Dog∨Cat
 cat : Cat → Dog∨Cat

data Cat∨Dog : Set where
 cat' : Cat → Cat∨Dog
 dog' : Dog → Cat∨Dog

Dog∨Cat→Cat∨Dog : Dog∨Cat → Cat∨Dog
Dog∨Cat→Cat∨Dog (dog myDogVar) = dog' myDogVar
Dog∨Cat→Cat∨Dog (cat myCatVar) = cat' myCatVar
-- ok so
-- you're on the right track there
-- dog constructor for Dog∨Cat takes an object of type Dog
-- so you think, ok i should be able to turn dog into dog', intuitively
-- and that's what you do, dog' constructor for Dog∨Cat takes an object of type Dog
-- you have one available from your "dog" constructor for Dog∨Cat, since you're in the
-- case for that constructor, so then you use that to construct a Cat∨Dog with that
-- object
-- the object gets created by (type name)? just by naming it? tis' type is inferred in this case?
-- the object gets created by (constructor {args-to-constructor}) (think like constructors for C++ classes)
-- okay

-- so, the objects in data-types are like syntax trees, the nodes are labeled by identifiers for the constructors
-- of the type (and whatever types are used as parameters to the constructors)

data Tree : Set where
 leaf : Tree
 node : Tree → Tree → Tree

myTree₁ : Tree
myTree₁ = node (node leaf leaf) leaf


data Nat : Set where
 zero : Nat
 1+ : Nat → Nat

height-of-leftmost-branch-of-tree : Tree → Nat
height-of-leftmost-branch-of-tree leaf = zero
height-of-leftmost-branch-of-tree (node t₁ t₂) = 1+ (height-of-leftmost-branch-of-tree t₁)

-- you recurse over the data-type by case-matching on the identifiers on the nodes in the
-- syntax trees of its objects



-- so, "d ∨ c" is supposed to be all one term? yes but it thought it was a variable named that.
-- I'm supposed to pattern match the Dog∨Cat right? yea (i'm not aware of if it can be proven otherwise)
-- so to make it look at "d v c" as all one input-term you would put it in parens
-- so, when you case-match over Dog∨Cat, you case match over all (object) constructors

{-
proof-of-sym-of-∨ : {A B : Set} → A ∨ B → B ∨ A -- i'll leave the proof for you
proof-of-sym-of-∨ x ∨ y = y ∨ x -- ?
-}
-- your proof must be of the following form:
{-
proof-of-sym-of-v x = y

where: 
x is an object of type A ∨ B, that you get to assume you have available
y is an object of type B ∨ A that you have to construct as output, given your assumptions
-}
-- so when you case match on A ∨ B, there should be a case for each constructor of A ∨ B
-- proof-of-sym-of-v = -- all I can think to do is try to use an equality operator hahaha
-- remember how you case-match for Bool? you can do the same for _∨_
-- you get an A ∨ B as input, can you manipulate it into a B ∨ A, in all cases (of the case-matching, if you use it)?


-- alright, as promised, identity types:
-- What do you wanna use _==_ , _≡_ or Id _ _ ?
-- Id makes most sense to me.

-- so, first, let's talk a bit about the difference between the LHS and RHS parameters of the top line
{-
LHS means you can't even talk about the type until you've given those parameters
so to even begin to talk about an identity type (according to the top line here) we
need to have provided the type of objects, and one of the objects in the type.
So, this means that every constructor will have to be of the form Id x _

RHS on the other hand is free to vary. So, if you had another object y available
you could have Id x y, but, you don't, this is a polymorphic type ({A : Set}, quantifies
over all Sets), and the only object you've assumed you have available is x (with that
(x : A) parameter from the LHS)

So, the only constructor you could really give here is....
-}
data Id {A : Set} (x : A) : A → Set where
 refl : Id x x -- this one, refl, short for reflexivity (of the Identity type)
 -- the params are: element of A, type A
 -- why can you just pass in A twice? what do you mean?
 -- in this 'refl : Id x x' are x and x arguments to the type Id? right
 -- like wouldn't it need to be, for example,
 -- (for Bools)
 -- refl : Id a Bool ?
 -- refl : Id x (typeof x)
 -- well, Id for Bools might be something more like

-- haha see what i mean about paramaters vs. indices? (indices are the RHS)
-- lol woops multiple problems here :)
-- ultimately the type-constructor/type-family is like: Bool → Bool → Set, i.e.
-- takes two Bools and returns a type that encodes the proposition of whether
-- those two Bools are the "same" Bool (wrt beta/eta equiv)
{-
# bad IdForBools for demonstrating difference between params & indices
data IdForBools (x : Bool) : Bool → Set where
 refl-true : IdForBools x true
 refl-false : IdForBools x false
-}

data IdForBools : Bool → Bool → Set where
 refl-true : IdForBools true true
 refl-false : IdForBools false false

{-
This just exhaustively runs through the (what's called) "canonical" objects
of Bool, b, and that b into this "IdForBools" relation with itself.

"canonical" objects is just fancy words for "the normal forms of a type"
like, every term of type Bool *will* beta/eta reduce to either "true" or "false"
so, those are the normal forms / canonical objects of the Bool type

what Id _ _ does is basically do this for you generically for all objects in all types
so.. Id basically returns whatever you give it, right? What's the point of that
no it doesn't return what you give it, IdForBools takes two bools and returns a type
that has a proof (refl) if the two bools are beta/eta equivalent, and doesn't have
a proof otherwise (and remember, "a Bool" isn't just "true" or "false", it's possibly
some complex term containing variables that doesn't reduce directly to true or false because
it only exists under assumptions. So Id is a way to check for structural equivelance between objects?
Right, or maybe more precisely "eventual syntactic equivalence". As in, when they're both in NF?
Right, and, when you're not under assumptions, anything you have will just be able to reduce to NF
and Id is really kinda trivial, but, when you're under assumptions and your terms contain
variables and you can't reduce things to NF until the function/proof you're defining gets called
on its parameters, Id type tells you that the terms *will* eventually reduce to the same NF,
once the function does get called on those parameters
-}

-- short for "congruence"; functions called on equals inputs give equal outputs.
cong : {A B : Set} → (f : A → B) → (x y : A) → Id x y → Id (f x) (f y)
cong f x .x refl = refl


-- here lemme blow your mind:

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

f[if-b-x-y]=[if-b-fx-fy] : {A B : Set} → (f : A → B) → (b : Bool) → (x y : A) → Id (f (if b then x else y)) (if b then (f x) else (f y))
f[if-b-x-y]=[if-b-fx-fy] f true x y = refl
f[if-b-x-y]=[if-b-fx-fy] f false x y = refl

-- program manipulation via proofs is fun
-- can we stop here? I'm getting a little filled up I think. yea np :)
-- alright :) This id stuff is still not clicking but I'm gonna let the rest of this stuff sink in and then try to tackle
-- that again tomorrow
-- probably a good idea, yea i was wondering if this would be too much to get into after all the rest
-- but you're catching on real quick, great progress :) thanks! Helps to have an awesome teach! whatever i can do :)
-- anyway i'll let go, catch ya tomorrow :) tty-then!


-- so there's the difference between the LHS & RHS
-- you gave the (x : Bool) on the LHS, so it *has* to be an argument
-- but on the other side you give Bool → Set, the second arg is free to vary


-- Since you have to provide an (x : A) before you can talk about the type you can
-- maybe think of this as "equality, *specifically* to x"
-- The equality here is literal syntactic equality, well, an extension of this
-- basically not much more than beta/eta equivalence (and what you can derive from
-- that, which is really just more beta/eta equivalences)

Id[zero,zero] : Id zero zero
Id[zero,zero] = refl

{-
Id[0,1] : Id zero (1+ zero)
Id[0,1] = refl

-- nope they don't beta/eta to something syntactically equal so this proof doesn't go through
-}

-- The bit more you get beyond equality based on beta/eta equivalence is what's called the J-rule
Id-sym : {A : Set} {x y : A} → Id x y → Id y x
Id-sym {A} {x} {.x} refl = refl

-- Basically the J-rule says that if you have a function/proposition like
-- (x y : A) → Id x y → <something>
-- it suffices to just prove:
-- x x refl = <proof-of-something-for-the-x-x-refl-case>
-- In type theory rule-sets in academia this is achieved through an explicit inference rule
-- which says exactly what i wrote above
-- Here in Agda it looks like it's performing the J-rule with a slightly more generalized and
-- philosophically motivated inference rule (or rules), if it's actually doing what i think it's doing

-- What I think it's doing is unification in your case-matching against the constructors
-- since the only constructor is refl : Id x x, this basically makes both vars unify to x, and
-- lets refl work, so in that Id-sym proof, when you're proving it you can think of it like:

{-
Id-sym : {A : Set} {x x : A} → Id x x → Id x x
-}
-- and that makes it less tricky , then you can just be like, oh I need:

{-
{A : Set}    {A}
{x : A}      {x}
{x : A}      {.x}   <-- "." for explicitly repeated vars
Id x x       refl
-------
Id x x       refl   <-- and then the proof is just trivial
-}

{-
Questions or do you wanna try transitivity?
-}
