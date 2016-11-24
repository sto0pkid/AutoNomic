module id3 where

open import Agda.Primitive public

{-
Id : ∀ α → (A : Set α) → (x y : A) → Set ω
Id α A x y = ∀ β → (IdT : A → A → Set β) → ((z : A) → IdT z z) → IdT x y
-}

Id' : ∀ {α} → {A : Set α} → (x y : A) → (∀ β → Set ((lsuc β) ⊔ α))
Id' {α} {A} x y = λ β → (IdT : A → A → Set β) → ((z : A) → IdT z z) → IdT x y

-- refl : ∀ α → (A : Set α) → (x : A) → Id α A x x
refl : ∀ {α} → {A : Set α} → (x : A) → (∀ β → Id' x x β)
refl {α} {A} x = λ β → (λ IdT refl' → refl' x)

{-
Id-symmetric : ∀ {α} → {A : Set α} → {x y : A} → (∀ β → Id' x y β) → (∀ β → Id' y x β)  
-}
Id-symmetric' : ∀ {α} → {A : Set α} → {x y : A} → (∀ β → Id' x y ((lsuc β) ⊔ α)) → (∀ β → Id' y x β)
Id-symmetric' {α} {A} {x} {y} p = λ β → p β (λ a b → Id' b a β) (λ a → (λ IdT ⟲ → ⟲ a))  

{-
Id-transitive : ∀ {α} → {A : Set α} → {x y z : A} → (∀ β → Id' x y β) → (∀ β → Id' y z β) → (∀ β → Id' x z β)
-}
 


{-
False : Set ω
False = ∀ α → (A : Set α) → A
-}

False' : ∀ α → Set (lsuc α)
False' α = (A : Set α) → A




{-
True : Set ω
True = ∀ α → (A : Set α) → A → A

unit : True
unit = λ α A x → x
-}

True' : ∀ α → Set (lsuc α)
True' α = (A : Set α) → A → A 

unit : ∀ α → True' α
unit = λ α A x → x






-- False→False : False → False
False→False : (∀ α → False' α) → (∀ α → False' α)
False→False ⊥ = ⊥

-- True→True : True → True
True→True : (∀ α → True' α) → (∀ α → True' α)
True→True ⊤ = ⊤

-- False→True : False → True
False→True : (∀ α → False' α) → (∀ α → True' α)
False→True ⊥ = unit

{-
¬ : ∀ α → (A : Set α) → Set ω
¬ α A = A → (∀ β → (B : Set β) → B)
-}

-- ¬[True→False] : (True → False) → False
¬[True→False] : ((∀ α → True' α)  → (∀ α → False' α)) → (∀ α → False' α)
¬[True→False] f = f unit

¬[True→False]' : (∀ α → True' α → False' α) → (∀ α → False' α)
¬[True→False]' f α = f α (unit α)




-- False≡False : Id (lsuc ω) (Set ω) False False
-- False≡False : ∀ α → Id (lsuc (lsuc α)) (Set (lsuc α)) (False α) (False α)
False≡False' : ∀ α → (∀ β → Id' (False' α) (False' α) β)
False≡False' α = λ β IdT ⟲ → ⟲ (False' α)

-- True≡True : Id (lsuc ω) (Set ω) True True
-- True≡True : ∀ α → Id (lsuc (lsuc α)) (Set (lsuc α)) (True α) (True α)
True≡True' : ∀ α → (∀ β → Id' (True' α) (True' α) β)
True≡True' α = λ β IdT ⟲ → ⟲ (True' α)

unit≡unit' : ∀ α → (∀ β → Id' (unit α) (unit α) β)
unit≡unit' α = λ β IdT ⟲ → ⟲ (unit α)

x≡x' : ∀ α → (A : Set α) → (x : A) → (∀ β → Id' x x β)
x≡x' a A x = λ β IdT ⟲ → ⟲ x







[A≡B]→[A→B]' : ∀ {α} → {A B : Set α} → (∀ β → Id' A B β) → A → B
[A≡B]→[A→B]' {α} {A} {B} p = p α (λ X Y → X → Y) (λ X → (λ x → x))


[a≡b]→[fa≡fb]' : 
 ∀ {α} → {A : Set α} → 
 ∀ {β} → {B : Set β} → 
 (f : A → B) → (x y : A) → 
 (p : ∀ γ → Id' x y γ) → 
 (∀ γ → Id' (f x) (f y) γ)
[a≡b]→[fa≡fb]' {α} {A} {β} {B} f x y p = λ γ IdT ⟲ → p γ (λ a b → IdT (f a) (f b)) (λ a → ⟲ (f a))




True≠False' : (∀ α → (∀ β → Id' (True' α) (False' α) β)) → (∀ β → (B : Set β) → B)
True≠False' p = ¬[True→False]' (λ α → ([A≡B]→[A→B]' (p α)))


{-
Bool : Set ω
Bool = ∀ α → (A : Set α) → A → A → A
-}

Bool' : ∀ α → Set (lsuc α)
Bool' α = (A : Set α) → A → A → A

true : ∀ α → Bool' α
true = λ α A t f → t

false : ∀ α → Bool' α
false = λ α A t f → f

not : (∀ α → Bool' α) → (∀ α → Bool' α)
not b = λ α A t f → b α A f t

and : (∀ α → Bool' α) → (∀ α → Bool' α) → (∀ α → Bool' α)
and x y = λ α A t f → x α A (y α A t f) (false α A t f)

or : (∀ α → Bool' α) → (∀ α → Bool' α) → (∀ α → Bool' α)
or x y =  λ α A t f → x α A (true α A t f) (y α A t f)

{-
IsTrue : Bool → Set ω
IsTrue b = λ β → b (True' β) (False' β)
-}

IsTrue : (∀ α → Bool' α) → (∀ α → (Set (lsuc α)))
IsTrue b = λ α → b (lsuc (lsuc α)) (Set (lsuc α)) (True' α) (False' α)

IsTrue' : ∀ α → Bool' (lsuc (lsuc α)) → Set (lsuc α)
IsTrue' α b = b (Set (lsuc α)) (True' α) (False' α)

true≠false : (∀ α → (∀ β → Id' (true α) (false α) β)) → (∀ α → (A : Set α) → A)
true≠false p = ⊥
 where
  [True≡False] : ∀ α → (∀ β → Id' (True' α) (False' α) β)
  [True≡False] = λ α → [a≡b]→[fa≡fb]' (IsTrue' α) (true (lsuc (lsuc α))) (false (lsuc (lsuc α))) (p (lsuc (lsuc α)))

  ⊥ : ∀ α → (A : Set α) → A
  ⊥ = True≠False' [True≡False]


{-
Nat : Set ω
Nat = ∀ α → (A : Set α) → A → (A → A) → A
-}

Nat' : ∀ α → Set (lsuc α)
Nat' α = (A : Set α) → A → (A → A) → A

zero : ∀ α → Nat' α
zero α = λ A z s → z

suc : ∀ α → Nat' α → Nat' α
suc α n = λ A z s → s (n A z s)

one : ∀ α → Nat' α
one α = (suc α) (zero α)

{-
one α = (λ n A z s → n A z s) (λ A z s → z)
one α = λ A z s → (λ A z s → z) A z s
one α = λ A z s → z
-}

add : ∀ α → Nat' α → Nat' α → Nat' α
add α n m = λ A z s → n A (m A z s) s


𝕤0≡0+1 : ∀ α → (∀ β → Id' ((suc α) (zero α)) (add α (zero α) (one α)) β)
𝕤0≡0+1 α = λ β IdT ⟲ → ⟲ (λ A z s → s z)

isZero : ∀ α → Nat' (lsuc α) → Bool' α
isZero α n = n (Bool' α) (true α) (λ b → (false α))

isZero-zero≡𝕥 : ∀ α → (∀ β → Id' (isZero α (zero (lsuc α))) (true α) β)
isZero-zero≡𝕥 α = λ β IdT ⟲ → ⟲ (λ A t f → t)

𝕥≡isZero-zero : ∀ α → (∀ β → Id' (true α) (isZero α (zero (lsuc α))) β)
𝕥≡isZero-zero α = λ β IdT ⟲ → ⟲ (λ A t f → t)

isZero-one≡𝕗 : ∀ α → (∀ β → Id' (isZero α (one (lsuc α))) (false α) β)
isZero-one≡𝕗 α = λ β IdT ⟲ → ⟲ (λ A t f → f)

isZero-𝕤x≡𝕗 : ∀ α → (x : Nat' (lsuc α)) → (∀ β → Id' (isZero α ((suc (lsuc α)) x)) (false α) β)
isZero-𝕤x≡𝕗 α x = λ β IdT ⟲ → ⟲ (λ A t f → f)

𝕗≡isZero-𝕤x : ∀ α → (x : Nat' (lsuc α)) → (∀ β → Id' (false α) (isZero α ((suc (lsuc α)) x)) β)
𝕗≡isZero-𝕤x α x = λ β IdT ⟲ → ⟲ (λ A t f → f)

{-
mul : ∀ α → Nat' α → Nat' α → Nat' α
mul α n m = λ A z s → n A (zero α A z s) (add α m)
-}

-- 1) 𝕤 x ≠ 𝕫 
{-
𝕤x≠𝕫 : ∀ α → (x : Nat' (lsuc α)) → (∀ β → Id' (suc (lsuc α) x) (zero (lsuc α)) β) → (∀ β → (B : Set β) → B)
𝕤x≠𝕫 α x p = ⊥
 where
  [isZero-𝕤x≡isZero-𝕫] : ∀ β → Id' (isZero α ((suc (lsuc α)) x)) (isZero α (zero (lsuc α))) β
  [isZero-𝕤x≡isZero-𝕫] =  [a≡b]→[fa≡fb]' (isZero α) ((suc (lsuc α)) x) (zero (lsuc α)) p 

  [𝕗≡𝕥] : ∀ β → Id' (false α) (true α) β
  [𝕗≡𝕥] = [

  ⊥


-}
