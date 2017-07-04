module poly2 where

open import Agda.Primitive public

Formation : ∀ α → Set (lsuc (lsuc α))
Formation α = Set (lsuc α)

Functor : ∀ α β → Set (lsuc (α ⊔ β))
Functor α β = Set α → Set β

Endofunctor : ∀ α → Set (lsuc α)
Endofunctor α = Functor α α

Endobifunctor : ∀ α → Formation α
Endobifunctor α = Set α → Set α → Set α



{-
data ⊥ : Set where
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
-}

⊥-Functor : ∀ {α} → Endofunctor α
⊥-Functor {α} A = A

⊥ : ∀ {α} → Formation α
⊥ {α} = {A : Set α} → ⊥-Functor A

𝟘 : ∀ {α} → Formation α
𝟘 {α} = ⊥ { α }

{-
data ⊤ : Set where
 ● : ⊤
-}

⊤ : ∀ {α} → Formation α
⊤ {α} = {A : Set α} → A → A

⊤-Functor : ∀ {α} → Endofunctor α
⊤-Functor {α} A = A → A

⊤' : ∀ {α} → Formation α
⊤' {α} = {A : Set α} → ⊤-Functor A

-- Constructor
● : ∀ {α} → ⊤ { α }
● x = x

-- Elimination


-- Equality

{-
data 𝔹 : Set where
 𝕥 : 𝔹
 𝕗 : 𝔹
-}
poly-𝔹 : Set (lsuc lzero)
poly-𝔹 = {A : Set} → A → A → A

poly-𝔹-F : Set → Set
poly-𝔹-F A = A → A → A

poly-𝔹' : Set (lsuc lzero)
poly-𝔹' = {A : Set} → poly-𝔹-F A

{-
ω-poly-𝔹 = ∀ {α} {A : Set α} → A → A → A
-}

{-
data ℕ : Set where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ
-}

ℕ-Functor : ∀ { α } → Endofunctor α
ℕ-Functor A = (A → (A → A) → A)

{-
ℕ-Functor' : ∀ {α} → Endofunctor α
ℕ-Functor' {α} A = ⊤ { α } → A
-}

-- Take 1:
-- Let's try not to go off into the universe-hierarchy, if we can help it.
-- We can't do what simpler-easier does because of the hierarchy:
{-
-- Set₁ != Set
Bool₁ : Set
Bool₁ = (A : Set) → A → A → A
-}
-- So maybe let's try moving (A : Set) to the LHS:

-- Take 2:
Bool₂ : Set → Set
Bool₂ A = A → A → A

true₂ : (A : Set) → Bool₂ A
true₂ A t f = t

false₂ : (A : Set) → Bool₂ A
false₂ A t f = f

-- the problem is that now we can't actually make an eliminator for Bool₂
if₂ : (A : Set) → Bool₂ A → A → A → A
if₂ A b t f = b t f 


-- Okay so maybe let's go up just one level:
-- Take 3:
Bool₃ : Set₁
Bool₃ = {A : Set} → A → A → A

true₃ : Bool₃
true₃ t f = t

false₃ : Bool₃
false₃ t f = f

if₃ : {A : Set} → Bool₃ → A → A → A
if₃ b t f = b t f


-- ok now we've got an eliminator for Bool, let's use it.
-- Let's assume we don't have anything else in the system besides
-- Bool₁ and the stuff we've defined around it. No inductive types.
-- What can we make a function to?

-- Let's try Bool₃:
not₃ : Bool₃ → Bool₃
not₃ b = b false₃ true₃


-- Set is available
-- But we can't generate any objects of Set without making an
-- inductive type though..
-- So let's try Set₁

simple-⊥ : Set₁
simple-⊥ = {A : Set} → A

simple-⊤ : Set₁
simple-⊤ = {A : Set} → A → A

-- But now our boolean true and false can't operate on this because
-- they only take objects in Set
{-
-- Set₂ != Set
Bool₃→Set₁ : Bool₃ → Set₁
Bool₃→Set₁ b = b simple-⊤ simple-⊥ 
-}

-- But if it starts taking objects in Set₁, then it will have to be of
-- type Set₂. Alright let's go up just one more level:

-- Take 4:
Bool₄ : Set₂
Bool₄ = {A : Set₁} → A → A → A

true₄ : Bool₄
true₄ t f = t

false₄ : Bool₄
false₄ t f = f

if₄ : {A : Set₁} → Bool₄ → A → A → A
if₄ b t f = b t f

-- But woops, we forgot that it's polymorphic, and has to take Set₁ as an
-- implict argument. But Set₁ is of type Set₂, so really Bool must be of
-- type Set₃.
{-
-- Set₂ != Set₁
Bool₄→Set₁ : Bool₄ → Set₁
Bool₄→Set₁ b = b simple-⊤ simple-⊥ 
-}

-- Take 5:
Bool₅ : Set₃
Bool₅ = {A : Set₂} → A → A → A

true₅ : Bool₅
true₅ t f = t

false₅ : Bool₅
false₅ t f = f

if₅ : {A : Set₂} → Bool₅ → A → A → A
if₅ b t f = b t f

Bool₅→Set₁ : Bool₅ → Set₁
Bool₅→Set₁ b = b simple-⊤ simple-⊥ 

--Hooray, we defined a function out of Bool
--it's equivalent to:

Bool₅→Set₁' : Bool₅ → Set₁
Bool₅→Set₁' b = if₅ b simple-⊤ simple-⊥

--if₅ gives a generalized eliminator out of Bool₅.

-- Alright, but what about all the other functions we might try to
-- define out of Bool₅? How about basic boolean functions?

not₅ : Bool₅ → Bool₅
not₅ b = b true₅ false₅

--ummm, wait a minute, when we pass true₅ and false₅ to b, which
--has type Bool₅ = {A : Set₂} → A → A → A, aren't we implicitly
--passing Bool₅ : Set₃ where we're expecting an argument of type Set₂ ?

--Here's what actually happened:
not₅' : Bool₅ → Bool₅
not₅' b {A} = b (true₅ { A }) (false₅ { A })

--Let's make this more clear by making the type arguments explicit:
--Take 6:

Bool₆ : Set₃
Bool₆ = (A : Set₂) → A → A → A

true₆ : Bool₆
true₆ A t f = t

false₆ : Bool₆
false₆ A t f = f

if₆ : (A : Set₂) → Bool₆ → A → A → A
if₆ A b t f = b A t f

Bool₆→Set₁ : Bool₆ → Set₁
Bool₆→Set₁ b = b Set₁ simple-⊤ simple-⊥ 

{-
--And we get the expected/desired behavior:
--Set₃ != Set₂
not₆ : Bool₆ → Bool₆
not₆ b = b Bool₆ true₆ false₆
-}

not₆ : Bool₆ → Bool₆
not₆ b = λ A → b (A → A → A) (false₆ A) (true₆ A)

not₆' : Bool₆ → Bool₆
not₆' b = λ A → if₆ (A → A → A) b (false₆ A) (true₆ A)

-- Alright, this seems to work but it breaks the form;
-- we want it to return false₆ when it gets true₆ as an
-- argument, not this other function we construct on-the-fly

-- But of course for that we'll have to make it be universe-polymorphic.

-- Take 7: 
-- Woops, can't do this:
{-
--Setω is not a valid type
Bool₇ = ∀ α (A : Set α) → A → A → A
-}

Bool₇ : ∀ α → Set (lsuc α)
Bool₇ α = (A : Set α) → A → A → A

-- Woops, can't do this anymore either;
-- where's the level argument to Bool₇ ?
{-
true₇' : Bool₇
-}

-- Alright let's give it one:
true₇ : ∀ α → Bool₇ α
true₇ α A t f = t

false₇ : ∀ α → Bool₇ α
false₇ α A t f = f

not₇ : ∀ α → Bool₇ (lsuc α) → Bool₇ α
not₇ α b = b ((A : Set α) → A → A → A) (false₇ α) (true₇ α) 

-- Well, now we've got a different instance of Bool at each Level.
-- Is there some particular instance that "is" Bool?

--What's this here?
not₇' : (∀ {β} {B : Set β} → B → B → B) → (∀ α → Bool₇ α)
not₇' b = λ α → b (false₇ α) (true₇ α)

--What about this?
not₇'' : (∀ {β} {B : Set β} → B → B → B) → (∀ α → Bool₇ α)
not₇'' b = λ α → b (false₇ α) (true₇ α)

--What about this?
not₇''' : (∀ β (B : Set β) → B → B → B) → (∀ α → (A : Set α) → A → A → A)
not₇''' b = λ α → b (lsuc α) ((A : Set α) → A → A → A) (λ A t f → f) (λ A t f → t)

id : ∀ α → (A : Set α) → A → A
id α A x = x

const : ∀ α → (A : Set α) → A → A → A
const = true₇

{-

𝕥 && 𝕥 = 𝕥
𝕥 && 𝕗 = 𝕗
𝕗 && 𝕥 = 𝕗
𝕗 && 𝕗 = 𝕗

_&&_ 𝕥 = id Bool
_&&_ 𝕗 = const 𝕗 
-}

{-

not₇' : (∀ {β} {B : Set β} → B → B → B) → (∀ α → Bool₇ α)
not₇' b = λ α → b (false₇ α) (true₇ α)

-}

-- does this properly represent "and" ?
and₇ : (∀ α → (A : Set α) → A → A → A) → ((∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A))
and₇ x y = λ α → x (lsuc α) ((A : Set α) → A → A → A) (y α) (false₇ α)

and₇' : (∀ α → (A : Set α) → A → A → A) → ((∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A))
and₇' x y = λ α A → x α (A → A → A) (y α A) (false₇ α A)

and₇'' : (∀ α → (A : Set α) → A → A → A) → ((∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A))
and₇'' x y = λ α A t f → x α A (y α A t f) (false₇ α A t f)



or₇ : (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A)
or₇ x y = λ α → x (lsuc α) ((A : Set α) → A → A → A) (true₇ α) (y α)

or₇' : (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A)
or₇' x y = λ α A t f → x α A (true₇ α A t f) (y α A t f)


-- Well, we know this can apply to anything of finite level, 
-- and we can make functions of type Bool → Bool, but 
-- we can't return canonical objects of type Bool directly.

-- ω can perhaps be interpreted as the fixed-point of lsuc.
-- lsuc ω = ω
-- Can we recover a consistent version of our fixed-points?

{-
data _≡_ {A : Set} : A → A → Set where
 refl : (x : A) → x ≡ x
-}


Id' : (A : Set) → A → A → Set₁
Id' A x y = (IdT : (B : Set) → B → B → Set) → ((z : A) → IdT A z z) → IdT A x y

Id : ∀ α → (A : Set α) → A → A → Set (lsuc α)
Id α A x y = (IdT : (B : Set α) → B → B → Set α) → ((z : A) → IdT A z z) → IdT A x y 


-- What about iterated identity types? Seems it goes up the universe-hierarchy.

-- What about higher-inductive types?
Interval : ∀ α → Set (lsuc α)
Interval α = (IntervalT : Set α) → (p1 : IntervalT) → (p2 : IntervalT) → (interval : Id α IntervalT p1 p2) → IntervalT

Interval' : ∀ α → Set (lsuc α)
Interval' α = (IntervalT : Set α) → 
 (p1 : IntervalT) → 
 (p2 : IntervalT) → 
 (interval : (IdT : (B : Set α) → B → B → Set α) → ((z : IntervalT) → IdT IntervalT z z) → IdT IntervalT p1 p2) →
 IntervalT


-- What about univalence?


-- Bool is not a recursive data-type so it doesn't need fixed-points
-- Let's try Nat
data ℕ : Set where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ

𝕫≡𝕫 : Id lzero ℕ 𝕫 𝕫
𝕫≡𝕫 id-t ⟲ = ⟲ 𝕫

Nat : ∀ α → Set (lsuc α)
Nat α = (A : Set α) → A → (A → A) → A

zero : ∀ α → Nat α
zero α = λ A z s → z

suc : ∀ α → Nat α → Nat α
suc α n = λ A z s → s (n A z s)



-- from simpler-easier:
natprim : ∀ α → (A : Set α) → A → (A → A) → Nat α → A
natprim α r z s n = n r z s

-- rearranged:
natprim' : ∀ α → Nat α → (A : Set α) → A → (A → A) → A
natprim' α n A z s = n A z s

-- but (A : Set α) → A → (A → A) → A ≡ Nat α
natprim'' : ∀ α → Nat α → Nat α
natprim'' α n = λ A z s → n A z s

-- but (λ A z s → n A z s) ≡ n
natprim''' : ∀ α → Nat α → Nat α
natprim''' α n = n

-- but wait, we could just keep n
-- elements do their own pattern-matching.

{-
not₇'' : (∀ {β} {B : Set β} → B → B → B) → (∀ α → Bool₇ α)
not₇'' b = λ α → b (false₇ α) (true₇ α)
-}


add : (∀ α → (A : Set α) → A → (A → A) → A) → (∀ α → (A : Set α) → A → (A → A) → A) → (∀ α → (A : Set α) → A → (A → A) → A)
add n m = λ α → n (lsuc α) ((A : Set α) → A → (A → A) → A) (m α) (suc α) 
{-
add' : (∀ α → (A : Set α) → A → (A → A) → A) → (∀ α → (A : Set α) → A → (A → A) → A) → (∀ α → (A : Set α) → A → (A → A) → A)
add' n m = λ α A z s → n α A (m α A z s) (suc α)
-}
{-
mul : (∀ α → (A : Set α) → A → (A → A) → A) → (∀ α → (A : Set α) → A → (A → A) → A) → (∀ α → (A : Set α) → A → (A → A) → A)
mul n m = λ α → n (lsuc α) ((A : Set α) →  A → (A → A) → A) (zero α) (add m) 
-}

{-
-- This corresponds to a functor:
NatF : ∀ α → Set α → Set α
NatF α A = 1 + A
-}
{-
Mu : (Set → Set) → Set
-}


Church : (∀ α → Set α → Set α) → ∀ α → Set (lsuc α)
Church F α = (R : Set α) → (F α R → R) → R
