module id4 where

open import Agda.Primitive public


-- The return type of IdT needs to be able to be any type, so that we can use
-- arbitrary dependent types in path induction:

Id : ∀ α → (A : Set α) → (x y : A) → (∀ β → Set ((lsuc β) ⊔ α))
Id α A x y = 
 λ β →                       -- 
 (IdT : A → A → Set β) → 
 ((z : A) → IdT z z) → 
 IdT x y

refl : ∀ α → (A : Set α) → (x : A) → (∀ β → Id α A x x β)
refl α A x = λ β IdT ⟲ → ⟲ x




Id-symmetric : ∀ α → (A : Set α) → (x y : A) → (∀ β → Id α A x y ((lsuc β) ⊔ α)) → (∀ β → Id α A y x β)
Id-symmetric α A x y p = λ β → p β (λ a b → Id α A b a β) (λ a → (λ I ⟲ → ⟲ a))

Id-symmetric₂ : ∀ α → (A : Set α) → (x y : A) → (∀ β → Id α A x y ((lsuc β) ⊔ α)) → (∀ β → Id α A x y β) → (∀ β → Id α A y x β)
Id-symmetric₂ α A x y p p' = λ β → p β (λ a b → Id α A a b β → Id α A b a β) (λ a x → x) (p' β)
 

Id-transitive : ∀ α → (A : Set α) → (x y z : A) → (∀ β → Id α A x y ((lsuc β) ⊔ α)) → (∀ β → Id α A y z β → Id α A x z β)
Id-transitive α A x y z p = λ β → p β (λ a b → Id α A b z β → Id α A a z β) (λ a x → x)

Id-transitive₂ : ∀ α → (A : Set α) → (x y z : A) → (∀ β → Id α A x y ((lsuc β) ⊔ α)) → (∀ β → Id α A y z β) → (∀ β → Id α A x z β)
Id-transitive₂ α A x y z p q = λ β → p β (λ a b → Id α A b z β → Id α A a z β) (λ a x → x) (q β)

Id-transitive₃ : ∀ α → (A : Set α) → (x y z : A) → (∀ β → Id α A x y ((lsuc β) ⊔ α)) → (∀ β → Id α A x y β) → (∀ β → Id α A y z β) → (∀ β → Id α A x z β)
Id-transitive₃ α A x y z p' p q = λ β → p' β (λ a b → Id α A a b β → Id α A b z β → Id α A a z β) (λ a a' x → x) (p β) (q β)




False' : ∀ α → Set (lsuc α)
False' α = (A : Set α) → A

True' : ∀ α → Set (lsuc α)
True' α = (A : Set α) → A → A

unit : ∀ α → True' α
unit α = λ A x → x




¬[True→False] : ((∀ α → True' α) → (∀ α → False' α)) → (∀ α → False' α)
¬[True→False] f = f unit

[A≡B]→[A→B] : ∀ α → (A B : Set α) → (∀ β → Id (lsuc α) (Set α) A B β) → A → B
[A≡B]→[A→B] α A B p = p α (λ X Y → X → Y) (λ X x → x)

{-
True≠False : (∀ α → (∀ β → Id (lsuc (lsuc α)) (Set (lsuc α)) (True' α) (False' α) β)) → (∀ β → (B : Set β) → B)
True≠False p = ¬[True→False] ([A≡B]→[A→B] (lsuc α) (True' α) (False' α) (p α))
-}

[a≡b]→[fa≡fb] : 
 ∀ α β → (A : Set α) → (B : Set β) →
 (f : A → B) → (x y : A) → (∀ γ → Id α A x y γ) → (∀ γ → Id β B (f x) (f y) γ)
[a≡b]→[fa≡fb] α β A B f x y p = λ γ IdT ⟲ → p γ (λ a b → IdT (f a) (f b)) (λ a → ⟲ (f a))

