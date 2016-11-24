module polymorphism where

open import Agda.Primitive public

id : (A : Set) → A → A
id A x = x

-- No Girard paradoxes
-- So no Type:Type
-- So no self-application
{-
-- Set₁ != Set
id-id : (A : Set) → A → A
id-id = id ((A : Set) → A → A) id
-}

id₁ : (A : Set₁) → A → A
id₁ A x = x

id₁-id : (A : Set) → A → A
id₁-id = id₁ ((A : Set) → A → A) id

{-
-- Set₂ != Set₁
id₁-id₁ : (A : Set₁) → A → A
id₁-id₁ = id₁ ((A : Set₁) → A → A) id₁
-}

id₂ : (A : Set₂) → A → A
id₂ A x = x

id₂-id₁ : (A : Set₁) → A → A
id₂-id₁ = id₂ ((A : Set₁) → A → A) id₁

{-

 id₃
 id₄
 id₅

 .
 .
 .

-}

-- how do we get from id-n to id-(n+1) ?
id-Lift : ∀ {n} → ((A : Set n) → A → A) → ((A : Set (lsuc n)) → A → A)
id-Lift id-n = λ A x → x

-- what would be the limit of repeated application of id-Lift?
-- something like "(A : Set ω) → A → A"
-- we can't do that, but with universe-polymorphism we can form
-- something equivalent:

id∞ : ∀ α → (A : Set α) → A → A
id∞ α A x = x
 
