module id2 where

open import Agda.Primitive public

-- Main thing: propositional identity
Id' : ∀ α → (A : Set α) → A → A → (∀ β → Set ((lsuc β) ⊔ α))
Id' α A x y β = (IdT : A → A → Set β) → ((z : A) → IdT z z) → IdT x y

{-
Id : ∀ α → (A : Set α) → A → A → Set ω
Id α A x y = ∀ β → (IdT : A → A → Set β) → ((z : A) → IdT z z) → IdT x y
-}

refl' : ∀ α → (A : Set α) → (x : A) → (∀ β → Id' α A x x β)
refl' α A x = λ β IdT refl'' → refl'' x 

--refl : ∀ α → (A : Set α) → (x : A) → Id α A x x
refl : ∀ α → (A : Set α) → (x : A) → (∀ β → (IdT : A → A → Set β) → ((z : A) → IdT z z) → IdT x x)
refl α A x = λ β IdT refl' → refl' x



-- Basic types to start with
False : ∀ α → Set (lsuc α)
False α = (A : Set α) → A

{-
False : Set ω
False = ∀ α → (A : Set α) → A
-}

¬' : ∀ α → (A : Set α) → Set (lsuc α)
¬' α A = A → False α

{-
¬ : ∀ α → (A : Set α) → Set ω
¬ α A = A → False
-}

True : ∀ α → Set (lsuc α)
True α = (A : Set α) → A → A

{-
True : Set ω
True = ∀ α → (A : Set α) → A → A
-}

unit' : ∀ α → True α
unit' α = λ A x → x


-- unit : True
unit : ∀ α → (A : Set α) → A → A
unit = λ α A x → x

-- Sanity implications:
False→False' : ∀ α → False α → False α
False→False' α ⊥ = ⊥

-- False→False : False → False
False→False : (∀ α → (A : Set α) → A) → (∀ α → (A : Set α) → A)
False→False ⊥ = ⊥


True→True' : ∀ α → True α → True α
True→True' α ⊤ = ⊤

-- True→True : True → True
True→True : (∀ α → (A : Set α) → A → A) → (∀ α → (A : Set α) → A → A)
True→True ⊤ = ⊤ 



False→True' : ∀ α → False α → True α
False→True' α ⊥ = unit' α

False→True : (∀ α → (A : Set α) → A) → (∀ α → (A : Set α) → A → A)
False→True f = unit



¬[True→False]' : ∀ α → (True α → False α) → False α
¬[True→False]' α f = f (unit α)

¬[True→False] : ((∀ α → (A : Set α) → A → A) → (∀ α → (A : Set α) → A)) → (∀ α → (A : Set α) → A)
¬[True→False] f = f unit


-- Sanity equalities:
--False≡False' : Id (lsuc (lsuc lzero)) (Set₁) (False lzero) (False lzero)
False≡False'₀ : ∀ β → (IdT : Set₁ → Set₁ → Set β) → (refl : (z : Set₁) → IdT z z) → IdT (False lzero) (False lzero)
False≡False'₀ = refl' (lsuc (lsuc lzero)) Set₁ (False lzero)


--False≡False' : ∀ α → Id (lsuc (lsuc α)) (Set (lsuc α)) (False α) (False α)
False≡False' : ∀ α → (∀ β → (IdT : Set (lsuc α) → Set (lsuc α) → Set β) → ((z : Set (lsuc α)) → IdT z z) → IdT (False α) (False α))
False≡False' α = refl' (lsuc (lsuc α)) (Set (lsuc α)) (False α)


{-
--False≡False : Id (lsuc ω) (Set ω) False False
False≡False : ∀ β → (IdT : Set ω → Set ω → Set β) → ((z : Set ω) → IdT z z) → IdT False False
False≡False = refl False
-}

True≡True' : ∀ α → (∀ β → (IdT : Set (lsuc α) → Set (lsuc α) → Set β) → ((z : Set (lsuc α)) → IdT z z) → IdT (True α) (True α))
True≡True' α = refl' (lsuc (lsuc α)) (Set (lsuc α)) (True α)


{-
--True≡True : Id (lsuc ω) (Set ω) True True
True≡True : ∀ β → (IdT : Set ω → Set ω → Set β) → ((z : Set ω) → IdT z z) → IdT True True
True≡True = refl True
-}

unit≡unit' : ∀ α → (∀ β → (IdT : True α → True α → Set β) → ((z : True α) → IdT z z) → IdT (unit α) (unit α))
unit≡unit' α = refl' (lsuc α) (True α) (unit α)


[A≡B]→[A→B]' : ∀ α → (A B : Set α) → (∀ β → (IdT : Set α → Set α → Set β) → ((z : Set α) → IdT z z) → IdT A B) → A → B
[A≡B]→[A→B]' α A B p = p α (λ X Y → X → Y) (λ X → (λ x → x))



[a≡b]→[fa≡fb]' : 
 ∀ α → (A : Set α) → 
 ∀ β → (B : Set β) → 
 (f : A → B) → (x y : A) → 
 (p : ∀ γ → (IdT : A → A → Set γ) → ((z : A) → IdT z z) → IdT x y) → 
 (∀ γ → (IdT : B → B → Set γ) → ((z : B) → IdT z z) → IdT (f x) (f y))
[a≡b]→[fa≡fb]' α A β B f x y p = λ γ IdT ⟲ → p γ (λ a b → IdT (f a) (f b)) (λ a → ⟲ (f a))



True≠False' : (∀ α → (∀ β → (IdT : Set (lsuc α) → Set (lsuc α) → Set β) → ((z : Set (lsuc α)) → IdT z z) → IdT (True α) (False α))) → (∀ β → (B : Set β) → B)
True≠False' p = λ β → ¬[True→False]' β ([A≡B]→[A→B]' (lsuc β) (True β) (False β) (p β))

{-
Bool : Set ω
Bool = ∀ α → (A : Set α) → A → A → A
-}

true : ∀ α → (A : Set α) → A → A → A
true = λ α A t f → t

false : ∀ α → (A : Set α) → A → A → A
false = λ α A t f → f

not : (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A)
not b = λ α A t f → b α A t f

and : (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A)
and x y = λ α A t f → x α A (y α A t f) (false α A t f)

or : (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A) → (∀ α → (A : Set α) → A → A → A)
or x y = λ α A t f → x α A (true α A t f) (y α A t f)

{-
IsTrue : (∀ α → (A : Set α) → A → A → A) → Set ω
IsTrue b = ∀ α → b (lsuc (lsuc α)) (Set (lsuc α)) (True α) (False α)
-}

{-
true≠false : (∀ α → (∀ β → (IdT : S
-}
