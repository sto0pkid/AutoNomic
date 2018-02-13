module Abstract where

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data _==_ {i} {A : Set i} (x : A) : A → Set i where
 refl : x == x

==-sym : ∀ {i} {A : Set i} {x y : A} → x == y → y == x
==-sym refl = refl

==-trans : ∀ {i} {A : Set i} {x y z : A} → x == y → y == z → x == z
==-trans refl refl = refl

abstract
 foo : Nat
 foo = zero

 foo==0 : foo == zero
 foo==0 = refl

 foo' : Nat
 foo' = suc (suc zero)

 foo'==2 : foo' == suc (suc zero)
 foo'==2 = refl

 countdown : Nat -> Nat
 countdown zero = zero
 countdown (suc n) = countdown n

-- recover the one-step reductions / definitional equalities:
 countdown[0]==0 : countdown zero == zero
 countdown[0]==0 = refl

 countdown[suc-n]==countdown[n] : ∀ (n : Nat) → countdown (suc n) == countdown n
 countdown[suc-n]==countdown[n] n = refl


 good-countdown : Nat → Nat
 good-countdown n = zero

 good-countdown[n]==0 : ∀ (n : Nat) → good-countdown n == zero
 good-countdown[n]==0 n = refl


cong : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → {x y : A} → x == y → (f x) == (f y)
cong f refl = refl

subst : ∀ {i j} {A : Set i} {P : A → Set j} → {x y : A} → P x → x == y → P y
subst hyp refl = hyp

_+_ : Nat → Nat → Nat
zero       + y = y
(suc x)    + y = suc (x + y)

_*_ : Nat → Nat → Nat
zero          * y = zero
(suc x)       * y = y + (x * y)

_^_ : Nat → Nat → Nat
y ^ zero    = (suc zero)
y ^ (suc x) = y * (y ^ x)


bad-countdown : Nat -> Nat
bad-countdown zero = zero
bad-countdown (suc n) = bad-countdown n

bad-countdown[n]==0 : ∀ (n : Nat) → Set
bad-countdown[n]==0 n = bad-countdown n == zero

{-
bad-countdown[2^256]==0 : bad-countdown (2 ^ 256) == 0
bad-countdown[2^256]==0 = refl

We can theoretically use refl as the proof, but it just runs and runs and runs
-}

countdown[n]==0 : ∀ (n : Nat) → Set
countdown[n]==0 n = countdown n == zero

{-
countdown[2^256]==0 : countdown (2 ^ 256) == 0
countdown[2^256]==0 = refl

But now we can't use 'refl' as the proof
This one at least just fails rather than going into a huge loop
-}

countdown[n]==0-ind : ∀ (n : Nat) → countdown n == zero → countdown (suc n) == zero
countdown[n]==0-ind n hyp = ==-trans (countdown[suc-n]==countdown[n] n) hyp


countdown[n]==0-proof : ∀ (n : Nat) → countdown n == zero
countdown[n]==0-proof zero = countdown[0]==0
countdown[n]==0-proof (suc n) = countdown[n]==0-ind n (countdown[n]==0-proof n)

-- perfect:
countdown[2^256]==0 : countdown (2 ^ 256) == 0
countdown[2^256]==0 = countdown[n]==0-proof (2 ^ 256)

[A==B]→[A→B] : {A B : Set} → A == B → A → B
[A==B]→[A→B] refl a = a

data ⊥ : Set where

omega : {A : Set} → ⊥ → A
omega ()

data ⊤ : Set where
 unit : ⊤

⊤≠⊥ : (⊤ == ⊥) → ⊥
⊤≠⊥ hyp = [A==B]→[A→B] hyp unit 

isZero : Nat → Set
isZero zero = ⊤
isZero (suc n) = ⊥

zero≠suc-x : {n : Nat} → (zero == (suc n)) → ⊥
zero≠suc-x hyp = ⊤≠⊥ (cong isZero hyp) 


data _≡_ : Nat → Nat → Set where
 ≡₁-base₀ : countdown zero ≡ zero
 ≡₁-baseₛ : {n : Nat} → countdown (suc n) ≡ countdown n
 ≡₂-base : {n : Nat} → good-countdown n ≡ zero
 ≡-sym : {x y : Nat} → x ≡ y → y ≡ x
 ≡-trans : {x y z : Nat} → x ≡ y → y ≡ z → x ≡ z
 

postulate
 funext : ∀ {i j} {A : Set i} {B : Set j} {f g : A → B} → ((x : A) → f x == g x) → f == g

countdown[n]==good-countdown[n] : (n : Nat) → countdown n == good-countdown n
countdown[n]==good-countdown[n] n = ==-trans (countdown[n]==0-proof n) (==-sym (good-countdown[n]==0 n))

countdown==good-countdown : countdown == good-countdown
countdown==good-countdown = funext countdown[n]==good-countdown[n]





path-size : {x y : Nat} → x ≡ y → Nat
path-size (≡-trans ≡₁ ≡₂) = suc ((path-size ≡₁) + (path-size ≡₂))
path-size (≡-sym ≡₁) = suc (path-size ≡₁)
path-size x = suc zero

postulate
 -- just as an example
 path-size-countdown[n]==suc-n : (n : Nat) → (p : countdown n ≡ zero) → path-size p == suc n

countdown[n]≡0==good-countdown[n]==0 : (n : Nat) → (countdown n ≡ zero) == (good-countdown n ≡ zero)
countdown[n]≡0==good-countdown[n]==0 n = cong (λ f → f n ≡ zero) countdown==good-countdown

{-
path-size-good-countdown[n]==suc-n : (n : Nat) → (p : good-countdown n ≡ zero) → path-size p == suc n
path-size-good-countdown[n]==suc-n n hyp = (path-size-countdown[n]==suc-n n ([A==B]→[A→B] (==-sym (countdown[n]≡0==good-countdown[n]==0 n)) hyp))
-- now how to coerce back to good-countdown?

-}


function-equality? : {A B : Set} → (f g : A → B) → f == g → (x : A) → (y : B) → (f x == y) == (g x == y)
function-equality? f g p x y = cong (λ h → h x == y) p

z==z : Set
z==z = zero == zero

[z==z]==[z==z] : Set₁
[z==z]==[z==z] = (zero == zero) == (zero == zero)




Nat==Nat : Set₁
Nat==Nat = Nat == Nat



{-
path-size-good-countdown[n]==suc-n : (n : Nat) → (p : good-countdown n ≡ zero) → path-size p == suc n
path-size-good-countdown[n]==suc-n n p = 


-}

{-
pathsize[countdown[n]]==suc-n : (n : Nat) → (p : countdown n ≡ zero) → path-size p ==
-}

{-
pathsize[countdown[n]]==pathsize[goodcountdown[n]] : (n : Nat) → (p₁ : countdown n ≡ zero) → (p₂ : good-countdown n ≡ zero) → path-size p₁ == path-size p₂
pathsize[countdown[n]]==pathsize[goodcountdown[n]] n p₁ p₂ = subst (λ p → path-size p₁ == p) countdown....

-- not sure if i can prove this
-}
-- so maybe something like this would actually work?

{-
[x≡y]→[x==y] : (x y : Nat) → x ≡ y → x == y
[x≡y]→[x==y] zero zero hyp = refl
[x≡y]→[x==y] zero (suc y) hyp = 
-}
