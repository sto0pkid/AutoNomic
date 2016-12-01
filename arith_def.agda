module arith_def where

open import Agda.Primitive public

{-
Arithmetical definability:

 http://www.cogsci.rpi.edu/~heuveb/teaching/Logic/CompLogic/Web/Presentations/Arithmetical%20Definability.pdf
-}

-- Logical expressions:

infix 2 _≡_
data _≡_ {A : Set} : A → A → Set where
 refl : (x : A) → x ≡ x

≡-sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
≡-sym (refl x) = refl x

≡-trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans (refl x) (refl .x) = refl x 



infix 1 _∨_
data _∨_ (A B : Set)  : Set where
 inl : A → A ∨ B
 inr : B → A ∨ B

infix 1 _∧_
data _∧_ (A B : Set) : Set where
 cons : A → B → A ∧ B

data ∃ (A : Set) (B : A → Set) : Set where
 _,_ : (x : A) → (y : B x) → ∃ A B

syntax ∃ A (λ x → e) = ∃ x ∈ A , e





-- Signature:
data ℕ : Set where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ

infix 3 _+_
_+_ : ℕ → ℕ → ℕ
𝕫 + m = m
(𝕤 n) + m = 𝕤 (n + m)

infix 4 _×_
_×_ : ℕ → ℕ → ℕ
𝕫 × m = 𝕫
(𝕤 n) × m = m + (n × m)




-- N-ary functions:
N-ary-level : Level → Level → ℕ → Level
N-ary-level ℓ₁ ℓ₂ 𝕫    = ℓ₂
N-ary-level ℓ₁ ℓ₂ (𝕤 n) = ℓ₁ ⊔ N-ary-level ℓ₁ ℓ₂ n

N-ary : ∀ {ℓ₁ ℓ₂} (n : ℕ) → Set ℓ₁ → Set ℓ₂ → Set (N-ary-level ℓ₁ ℓ₂ n)
N-ary 𝕫    A B = B
N-ary (𝕤 n) A B = A → N-ary n A B


-- Example arithmetical definitions:

infix 2 _<_
_<_ : ℕ → ℕ → Set
x < y = ∃ z ∈ ℕ , x + 𝕤 z ≡ y

infix 2 _≤_
_≤_ : ℕ → ℕ → Set
x ≤ y = ∃ z ∈ ℕ , x + z ≡ y

pred : ℕ → ℕ → Set
pred x y = (x ≡ 𝕫 ∧ y ≡ 𝕫) ∨ (x ≡ 𝕤 y)

diff : ℕ → ℕ → ℕ → Set
diff x y z = (x ≤ y ∧ z ≡ 𝕫) ∨ (x ≡ y + z)

quo : ℕ → ℕ → ℕ → Set
quo x y z = (y ≡ 𝕫 ∧ z ≡ 𝕫) ∨ (∃ w ∈ ℕ , (w < y ∧ y × z + w ≡ x))

rem : ℕ → ℕ → ℕ → Set
rem x y z = (y ≡ 𝕫 ∧ z ≡ x) ∨ (z < y ∧ (∃ w ∈ ℕ , (y × w + z ≡ x)))

rem' : ℕ → ℕ → ℕ → Set
rem' x y z = ∃ w ∈ ℕ , (quo x y w ∧ y × w + z ≡ x)


-- Still less than:
[x≡y]→[fx≡fy] : {A B : Set} → (f : A → B) → (x y : A) → x ≡ y → f x ≡ f y
[x≡y]→[fx≡fy] f x .x (refl .x) = refl (f x)

pred-func : ℕ → ℕ
pred-func 𝕫 = 𝕫
pred-func (𝕤 n) = n

[𝕤n≡𝕤m]→[n≡m] : (n m : ℕ) → (𝕤 n ≡ 𝕤 m) → n ≡ m
[𝕤n≡𝕤m]→[n≡m] n m hyp = [x≡y]→[fx≡fy] pred-func (𝕤 n) (𝕤 m) hyp

[n+𝕫≡n]-base : 𝕫 + 𝕫 ≡ 𝕫
[n+𝕫≡n]-base = refl 𝕫

[n+𝕫≡n]-ind : (n : ℕ) → n + 𝕫 ≡ n → (𝕤 n) + 𝕫 ≡ (𝕤 n)
[n+𝕫≡n]-ind n [n+𝕫≡n] = [x≡y]→[fx≡fy] 𝕤 (n + 𝕫) n [n+𝕫≡n]

n+𝕫≡n : (n : ℕ) → n + 𝕫 ≡ n
n+𝕫≡n 𝕫 = [n+𝕫≡n]-base
n+𝕫≡n (𝕤 n) = [n+𝕫≡n]-ind n (n+𝕫≡n n)

n≡n+𝕫 : (n : ℕ) → n ≡ n + 𝕫
n≡n+𝕫 n = ≡-sym (n+𝕫≡n n)



[𝕤n+k≡𝕤m]→[n+k≡m]-base : (n m : ℕ) → (𝕤 n) + 𝕫 ≡ 𝕤 m → n + 𝕫 ≡ m
[𝕤n+k≡𝕤m]→[n+k≡m]-base n m hyp = (≡-trans (n+𝕫≡n n) ([𝕤n≡𝕤m]→[n≡m] n m (≡-trans (n≡n+𝕫 (𝕤 n)) hyp)))

[𝕤n+k≡𝕤m]→[n+k≡m]-ind : (n m k : ℕ) → ((𝕤 n) + k ≡ (𝕤 m) → n + k ≡ m) → (𝕤 n) + (𝕤 k) ≡ (𝕤 m) → n + (𝕤 k) ≡ m
[𝕤n+k≡𝕤m]→[n+k≡m]-ind n m k hyp [𝕤n+𝕤k≡𝕤m] = [𝕤n≡𝕤m]→[n≡m] (n + (𝕤 k)) m [𝕤n+𝕤k≡𝕤m]


[𝕤n+k≡𝕤m]→[n+k≡m] : (n m k : ℕ) → (𝕤 n) + k ≡ 𝕤 m → n + k ≡ m
[𝕤n+k≡𝕤m]→[n+k≡m] n m 𝕫 = [𝕤n+k≡𝕤m]→[n+k≡m]-base n m 
[𝕤n+k≡𝕤m]→[n+k≡m] n m (𝕤 k) = [𝕤n+k≡𝕤m]→[n+k≡m]-ind n m k ([𝕤n+k≡𝕤m]→[n+k≡m] n m k)


[𝕤n<𝕤m]→[n<m] : (n m : ℕ) → (𝕤 n) < (𝕤 m) → n < m
[𝕤n<𝕤m]→[n<m] n m (z , [𝕤n+𝕤z≡𝕤m]) = (z , [𝕤n+k≡𝕤m]→[n+k≡m] n m (𝕤 z) [𝕤n+𝕤z≡𝕤m])

[𝕤n≤𝕤m]→[n≤m] : (n m : ℕ) → (𝕤 n) ≤ (𝕤 m) → n ≤ m
[𝕤n≤𝕤m]→[n≤m] n m (z , [𝕤n+z≡𝕤m]) = (z , [𝕤n+k≡𝕤m]→[n+k≡m] n m z [𝕤n+z≡𝕤m])


-- Non-empty vectors:
data NEVec (A : Set) : ℕ → Set where
 const : (x : A) → NEVec A (𝕤 𝕫)
 _::_ : {n : ℕ} → (x : A) → (xs : NEVec A n) → NEVec A (𝕤 n)

NE-head : {A : Set} → {n : ℕ} → NEVec A (𝕤 n) → A
NE-head (const x) = x
NE-head (x :: xs) = x


NE-Vec-proj : {A : Set} → (n : ℕ) → (i : ℕ) → (i < (𝕤 n)) → NEVec A (𝕤 n) → A
NE-Vec-proj 𝕫 i in-range vec = NE-head vec
NE-Vec-proj (𝕤 n) 𝕫 in-range (x :: xs) = x
NE-Vec-proj (𝕤 n) (𝕤 i) in-range (x :: xs) = NE-Vec-proj n i ([𝕤n<𝕤m]→[n<m] i (𝕤 n) in-range) xs

-- All primitive recursive functions are arithmetically definable.

zero : ℕ → ℕ → Set
zero x y = y ≡ 𝕫

suc : ℕ → ℕ → Set
suc x y = y ≡ 𝕤 x

id : (n : ℕ) → (i : ℕ) → (i < 𝕤 n) → NEVec ℕ (𝕤 n) → ℕ → Set
id n i in-range vec y = y ≡ NE-Vec-proj n i in-range vec

{-
comp : (k m : ℕ) → (f : NEVec ℕ (𝕤 k)) → (~g : NEVec (NEVec ℕ (𝕤 m) → ℕ) (𝕤 k)) → (~x : NEVec ℕ (𝕤 m)) → Set
comp k m f ~g ~x = NEVec  
-}
