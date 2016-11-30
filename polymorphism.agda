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

-- pseudo-self-application: 
id∞-id∞ : ∀ α → (A : Set α) → A → A
id∞-id∞ α = id∞ (lsuc α) ((A : Set α) → A → A) (id∞ α)

id∞' : ∀ {α} {A : Set α} → A → A
id∞' x = x

-- and with the polymorphism arguments made implicit, it looks
-- like regular self-application:
id∞'-id∞' : ∀ {α} {A : Set α} → A → A
id∞'-id∞' = id∞' id∞' 

data ℕ : Set where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ

add : ℕ → ℕ → ℕ
add 𝕫 y = y
add (𝕤 x) y = 𝕤 (add x y) 

mul : ℕ → ℕ → ℕ
mul 𝕫 y = 𝕫
mul (𝕤 x) y = add y (mul x y)

fac : ℕ → ℕ
fac 𝕫 = (𝕤 𝕫)
fac (𝕤 x) = mul (𝕤 x) (fac x)

almost-fac : (ℕ → ℕ) → (ℕ → ℕ)
almost-fac f 𝕫 = (𝕤 𝕫)
almost-fac f (𝕤 x) = mul (𝕤 x) (f x)

{-
Y : ∀ {α} → {A : Set α} → (∀ {β} → {B : Set β} → (A → A) → (A → A)) → A → A
Y {α} {A} f = f (Y f)
-}

Y : (∀ α → (A : Set α) → A → A) → (∀ α → (A : Set α) → A → A)
Y x α = x (lsuc α) ((A : Set α) → A → A) (x α)

Y' : (∀ α → (A : Set α) → A → A) → (∀ α → (A : Set α) → A → A)
Y' x α =  

