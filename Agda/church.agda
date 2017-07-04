module church where

open import Agda.Primitive public

False : ∀ α → Set (lsuc α)
False α = (A : Set α) → A

¬ : ∀ α β → Set β → Set (β ⊔ lsuc α)
¬ α β A = A → False α

True : ∀ α → Set (lsuc α)
True α = (A : Set α) → A → A

unit : ∀ α → True α
unit α = λ A x → x

Id : ∀ α → (A : Set α) → A → A → Set (lsuc α)
Id α A x y = (IdT : (B : Set α) → B → B → Set α) → ((z : A) → IdT A z z) → IdT A x y

Id' : ∀ α → (A : Set α) → A → A → Set (lsuc α)
Id' α A x y = (IdT : A → A → Set α) → ((z : A) → IdT z z) → IdT x y

Id₂ : ∀ α β → (A : Set α) → A → A → Set ((lsuc β) ⊔ α)
Id₂ α β A x y = (IdT : A → A → Set β) → ((z : A) → IdT z z) → IdT x y

{-
IdSet : ∀ α → (A B : Set α) → Set (lsuc α)
IdSet α A B = (IdT : Set α → Set α → Set α) → ((z : Set α) → IdT z z) → IdT A B
-}

Neq : ∀ α → (A : Set α) → A → A → Set (lsuc α)
Neq α A x y = Id α A x y → False α

unit≡unit : ∀ α → Id (lsuc α) (True α) (unit α) (unit α)
unit≡unit α = λ IdT refl → refl (unit α)

[unit≡unit]' : ∀ α → Id' (lsuc α) (True α) (unit α) (unit α)
[unit≡unit]' α = λ IdT refl → refl (unit α)

True≡True : ∀ α → Id (lsuc (lsuc α)) (Set (lsuc α)) (True α) (True α)
True≡True α = λ IdT refl → refl (True α)

[True≡True]' : ∀ α → Id' (lsuc (lsuc α)) (Set (lsuc α)) (True α) (True α)
[True≡True]' α = λ IdT refl → refl (True α)

False≡False : ∀ α → Id (lsuc (lsuc α)) (Set (lsuc α)) (False α) (False α)
False≡False α = λ IdT refl → refl (False α)

[False≡False]' : ∀ α → Id' (lsuc (lsuc α)) (Set (lsuc α)) (False α) (False α)
[False≡False]' α = λ IdT refl → refl (False α)

True→True : ∀ α → True α → True α
True→True α ⊤ = ⊤

False→False : ∀ α → False α → False α
False→False α ⊥ = ⊥

False→True : ∀ α → False α → True α
False→True α ⊥ = unit α

¬[True→False] : ∀ α → ¬ α (lsuc α) (True α → False α)
¬[True→False] α f = f (unit α)

[A→B]-func : ∀ α → Set α → Set α → Set α
[A→B]-func α A B = A → B

{-
[A≡B]→[A→B] : ∀ α → (A B : Set α) → Id' (lsuc α) (Set α) A B → A → B
[A≡B]→[A→B] α A B p = p (λ X Y → X → Y) (λ Z X → X)
-}

{-
Id' : ∀ α → (A : Set α) → A → A → Set (lsuc α)
Id' α A x y = (IdT : A → A → Set α) → ((z : A) → IdT z z) → IdT x y
-}

[A≡B]→[A→B] : ∀ α → (A B : Set α) → ((IdT : Set α → Set α → Set α) → ((z : Set α) → IdT z z) → IdT A B) → A → B
[A≡B]→[A→B] α A B p = p (λ X Y → X → Y) (λ z → (λ x → x))



[A≡B]→[A→B]' : ∀ α → (A B : Set α) → Id₂ (lsuc α) α (Set α) A B → A → B
[A≡B]→[A→B]' α A B p = p (λ X Y → X → Y) (λ z → (λ x → x)) 


True≠False : ∀ α → Id₂ (lsuc (lsuc α)) (lsuc α) (Set (lsuc α)) (True α) (False α) → False α
True≠False α p = ¬[True→False] α ([A≡B]→[A→B]' (lsuc α) (True α) (False α) p)
{-
True≠False' : ∀ α β γ → Id'' (lsuc (lsuc α)) β (Set (lsuc α)) (True α) (False α) → False γ
True≠False' α β γ p = 
-}

Bool : ∀ α → Set (lsuc α)
Bool α = (A : Set α) → A → A → A

true : ∀ α → Bool α
true α = λ A t f → t

false : ∀ α → Bool α
false α = λ A t f → f

IsTrue : ∀ α → Bool (lsuc (lsuc α)) → Set (lsuc α)
IsTrue α b = b (Set (lsuc α)) (True α) (False α)

[a≡b]→[fa≡fb] : ∀ α β → (A : Set α) → (B : Set β) → (f : A → B) → (x y : A) → Id₂ α (lsuc β) A x y → Id₂ β β B (f x) (f y)
[a≡b]→[fa≡fb] α β A B f x y p = p (λ a b → Id₂ β β B (f a) (f b)) (λ a → (λ IdT refl → refl (f a))) 

{-
true≠false : ∀ α → Id'' (lsuc (lsuc (lsuc α))) (lsuc (lsuc (lsuc α))) (Bool (lsuc (lsuc α))) (true (lsuc (lsuc α))) (false (lsuc (lsuc α))) → False (lsuc (lsuc α))
true≠false α p = [False]
 where
  [True≡False] : Id'' (lsuc (lsuc α)) (lsuc (lsuc α)) (Set (lsuc α)) (True α) (False α)
  [True≡False] = [a≡b]→[fa≡fb] (lsuc (lsuc (lsuc α))) (lsuc (lsuc α)) (Bool (lsuc (lsuc α))) (Set (lsuc α)) (IsTrue α) (true (lsuc (lsuc α))) (false (lsuc (lsuc α))) p 

  [False] : False (lsuc (lsuc α))
  [False] = True≠False α [True≡False]
-}
Nat : ∀ α → Set (lsuc α)
Nat α = (A : Set α) → A → (A → A) → A

zero : ∀ α → Nat α
zero α = λ A z s → z

suc : ∀ α → Nat α → Nat α
suc α n = λ A z s → n A z s

add : ∀ α → Nat α → Nat α → Nat α
add α n m = λ A z s → n A (m A z s) s



