module poly where


open import Agda.Primitive public

{-

module : basic defs

-}

ℓ : Set
ℓ = Level

ℓ₀ : ℓ
ℓ₀ = lzero

ℓ₁ : ℓ
ℓ₁ = lsuc ℓ₀

ℓ₂ : ℓ
ℓ₂ = lsuc ℓ₁

★ : (α : ℓ) → Set (lsuc α)
★ α = Set α

★₀ : ★ ℓ₁
★₀ = ★ ℓ₀

★₁ : ★ ℓ₂
★₁ = ★ ℓ₁

--syntax {x : A} → e = ∀ { x ∈ A }, e 

-- Lifting
record Lift {α ℓ} (A : ★ α) : ★ (α ⊔ ℓ) where
 constructor lift
 field lower : A

open Lift 

-- Identity function
id : ∀ {α}{A : ★ α} → A → A
id x = x

const : ∀ {α β} {A : ★ α} {B : ★ β} → A → B → A
const x = λ b → x

flip : ∀ {α β γ} {A : ★ α} {B : ★ β} {C : A → B → ★ γ} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

_$_ : ∀ {α β} {A : ★ α} {B : A → ★ β} → 
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

_<_>_ : ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} → 
        A → (A → B → C) → B → C
x < f > y = f x y

-- Function composition
_∘_ : 
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} →
 (B → C) → (A → B) → (A → C)

(g ∘ f) a = g (f a)

infixr 2 _∘_


-- Basic propositions:

--False
data ⊥ : ★₀ where
ω : ∀ {α} {A : ★ α} → ⊥ → A
ω ()

poly-⊥-F : Set → Set
poly-⊥-F A = A

poly-⊥ : Set (lsuc lzero)
poly-⊥ = (A : Set) → poly-⊥-F A

--True
data ⊤ : ★₀ where
 ● : ⊤

poly-⊤-F : Set → Set
poly-⊤-F A = A → A

poly-⊤ : Set (lsuc lzero)
poly-⊤ = (A : Set) → poly-⊤-F A

poly-idT-F : Set → Set
poly-idT-F = poly-⊤-F

poly-idT : Set (lsuc lzero)
poly-idT = (A : Set) → poly-idT-F A

poly-● : {A : Set} → poly-⊤-F A
poly-● a = a

poly-id : {A : Set} → poly-idT-F A
poly-id a = a



--"Agda needs to know about the unit type since some of the primitive operations in the reflected type checking monad return values in the unit type."
--http://agda.readthedocs.io/en/latest/language/built-ins.html#the-unit-type 
--{-# BUILTIN UNIT ⊤ #-}


-- Not
¬ : ∀ {α} → ★ α → ★ α
¬ A = A → ⊥



data Decidable {p} (P : ★ p) : ★ p where
 decidable : (p : P) → Decidable P
 undecidable : (¬p : ¬ P) → Decidable P


-- Or
data _∨_ {α β} (A : ★ α) (B : ★ β) : ★ (α ⊔ β) where
 ∨-cons1 : A → A ∨ B
 ∨-cons2 : B → A ∨ B 
infixr 0 _∨_

poly-∨-F : ∀ {α β γ} → Set α → Set β → Set γ → Set (γ ⊔ (β ⊔ α))
poly-∨-F {α} {β} {γ} A B C = (A → C) → (B → C) → C

poly-∨ : ∀ {α β γ} → Set α → Set β → Set ((lsuc γ) ⊔ (β ⊔ α)) 
poly-∨ {α} {β} {γ} A B = (C : Set γ) → poly-∨-F A B C

poly-inl : ∀ {α β γ} → (A : Set α) → (B : Set β) → A → poly-∨ { α } { β } { γ } A B
poly-inl A B a = λ C inl inr → inl a

poly-inr : ∀ {α β γ} → (A : Set α) → (B : Set β) → B → poly-∨ { α } { β } { γ } A B
poly-inr A B b = λ C inl inr → inr b





_∨'_ : (A : ★₀) (B : ★₀) → ★₁
A ∨' B = (C : ★₀) → (A → C) → (B → C) → C

-- And
data _∧_ {α β} (A : ★ α) (B : ★ β) : ★ (α ⊔ β) where
 ∧-cons : A → B → A ∧ B
infixr 0 _∧_

∧-π₁ : ∀ {α β} {A : ★ α} {B : ★ β} → A ∧ B → A
∧-π₁ (∧-cons a b) = a

∧-π₂ : ∀ {α β} {A : ★ α} {B : ★ β} → A ∧ B → B
∧-π₂ (∧-cons a b) = b


-- Pi
Π : ∀ {α β} (A : ★ α) (B : A → ★ β) → ★ (α ⊔ β)
Π A B = (a : A) → B a

syntax Π A (λ x → e) = Π x ∈ A , e



-- There exists
data ∃ {α β} (A : ★ α) (B : A → ★ β) : ★ (α ⊔ β) where
 _,_ : (x : A) (y : B x) → ∃ A B

poly-∃-F : ∀ {α β γ} → (A : Set α) → (A → Set β) → Set γ → Set (γ ⊔ (α ⊔ β))
poly-∃-F {α} {β} {γ} A B C = ((x : A) (y : B x) → C) → C


syntax ∃ A (λ x → e) = ∃ x ∈ A , e

π₁ : ∀ {α β} {A : ★ α} {B : A → ★ β} → (∃ x ∈ A , B x) → A
π₁ (x , y) = x

π₂ : ∀ {α β} {A : ★ α} {B : A → ★ β} → (∃AB : ∃ x ∈ A , B x) → B (π₁ ∃AB)
π₂ (x , y) = y




--bi-implication
_⇆_ : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
A ⇆ B = (A → B) ∧ (B → A)
infixr 0 _⇆_ 


_↔_ : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
_↔_ A B = (A → B) ∧ (B → A)
infix 0 _↔_

--non-existence
∄ : ∀ {α β} (A : ★ α) (P : A → ★ β) → ★ (α ⊔ β)
∄ A P = ¬ ( ∃ x ∈ A , P x ) 

syntax ∄ A (λ x → e) = ∄ x ∈ A , e


--Identity types


--These form propositions out of (typically) objects, so
--we want them to bind tighter than operators like ∧ and ∨ which
--connect propositions into larger propositions
data _≡_ {α} {A : ★ α} : A → A → ★ α where
 ⟲ : (x : A) → x ≡ x
infixr 1 _≡_ 

-- Inequality
_≠_ : ∀ {α} {A : ★ α} (x y : A) → ★ α
_≠_ x y = ¬ (x ≡ y)
infixr 1 _≠_



-- uniqueness
unique : 
 ∀ {α β} {A : ★ α} (P : A → ★ β) (a : A) → 
 ★ (α ⊔ β)
unique {α} {β} {A} P a = ∀ (a' : A) (p : P a') → a ≡ a'


--unique existence
∃! : ∀ {α β} (A : ★ α) (P : A → ★ β) → ★ (α ⊔ β)
∃! A P = ∃ x ∈ A , (Π y ∈ A , (P x ⇆ x ≡ y))

syntax ∃! A (λ x → e) = ∃! x ∈ A , e

∃!₂ : ∀ {α β} (A : ★ α) (P : A → ★ β) → ★ (α ⊔ β)
∃!₂ A P = ∃ x ∈ A , (P x ∧ ∄ y ∈ A , (P y ∧ y ≠ x))

∃!₃ : ∀ {α β} (A : ★ α) (P : A → ★ β) → ★ (α ⊔ β)
∃!₃ A P = ∃ x ∈ A , (P x ∧ Π y ∈ A , (P y → y ≡ x))

∃!₄ : ∀ {α β} (A : ★ α) (P : A → ★ β) → ★ (α ⊔ β)
∃!₄ A P = (∃ x ∈ A , P x) ∧ ((y z : A) → ((P y ∧ P z) → y ≡ z))
   
{- prove that these 4 definitions are equivalent -}


-- propositions about properties:
-- reflexivity
reflexive : ∀ {α β} {A : ★ α} (P : A → ★ β) → ★ (α ⊔ β)
reflexive {α} {β} {A} P = Π x ∈ A , P x

irreflexive : ∀ {α β} {A : ★ α} (P : A → ★ β) → ★ (α ⊔ β)
irreflexive {α} {β} {A} P = Π x ∈ A , (P x → ⊥)


-- symmetric
symmetric : ∀ {α β} {A : ★ α} (P : A → A → ★ β) → ★ (α ⊔ β)
symmetric {α} {β} {A} P = {x y : A} → P x y → P y x 

asymmetric : ∀ {α β} {A : ★ α} (P : A → A → ★ β) → ★ (α ⊔ β)
asymmetric {α} {β} {A} P = {x y : A} → P x y → P y x → ⊥

antisymmetric : ∀ {α β} {A : ★ α} (P : A → A → ★ β) → ★ (α ⊔ β)
antisymmetric {α} {β} {A} P = {x y : A} → P x y → P y x → x ≡ y


-- transitivity
transitive : ∀ {α β} {A : ★ α} (P : A → A → ★ β) → ★ (α ⊔ β)
transitive {α} {β} {A} P = {x y z : A} → P x y → P y z → P x z



-- fibers
fiber : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → (b : B) → ★ (α ⊔ β)
fiber {α} {β} {A} {B} f b = ∃ a ∈ A , (f a ≡ b) 


Fibers : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
Fibers {α} {β} {A} {B} f = ∃ b ∈ B , (fiber f b)


NoFibers : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
NoFibers {α} {β} {A} {B} f = ∃ b ∈ B , ((fiber f b) → ⊥)

fibrate : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → A → Fibers f
fibrate {α} {β} {A} {B} f a = ( f a , ( a , ⟲ (f a))) 

unfibrate : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → Fibers f → A
unfibrate {α} {β} {A} {B} f fib = π₁ (π₂ fib)


-- injections, surjections, bijections
injection : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
injection {α} {β} {A} {B} f = (a1 a2 : A) → (f a1 ≡ f a2) → (a1 ≡ a2)

surjection : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
surjection {α} {β} {A} {B} f = (b : B) → fiber f b 

bijection : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
bijection {α} {β} {A} {B} f = (injection f) ∧ (surjection f) 


-- two sets are related by injectivity if there is an injection between them
injective : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
injective {α} {β} A B = ∃ f ∈ (A -> B) , (injection f)

-- etc..
surjective : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
surjective {m} {n} A B = ∃ f ∈ (A -> B) , (surjection f)


bijective : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
bijective {α} {β} A B = (injective A B) ∧ (surjective A B)



-- Isomorphism:
data _≅_ {α} (A B : ★ α) : ★ α where
    ≅-cons : (f : A → B) → (g : B → A) → ((a : A) → (g ∘ f) a ≡ a) ∧ ((b : B) → (f ∘ g) b ≡ b ) → A ≅ B   

infixr 1 _≅_

-- Extract the components of an isomorphism:
≅-π₁ : ∀ {α} {A : ★ α} {B : ★ α} (P : A ≅ B) → (A → B)
≅-π₁ (≅-cons f g fg-inv) = f

[A≅B]→[A→B] : ∀ {α} {A : ★ α} {B : ★ α} (P : A ≅ B) → (A → B)
[A≅B]→[A→B] (≅-cons f g [g≡f⁻¹]) = f

≅-π₂ : ∀ {α} {A : ★ α} {B : ★ α} (P : A ≅ B) → (B → A)
≅-π₂ (≅-cons f g fg-inv) = g 

[A≅B]→[B→A] : ∀ {α} {A : ★ α} {B : ★ α} (P : A ≅ B) → (B → A)
[A≅B]→[B→A] (≅-cons f g fg-inv) = g

≅-π₃ : ∀ {α} {A : ★ α} {B : ★ α} (P : A ≅ B) → ((a : A) → ((≅-π₂ P) ∘ (≅-π₁ P)) a ≡ a) ∧ ((b : B) → ((≅-π₁ P) ∘ (≅-π₂ P)) b ≡ b )
≅-π₃ (≅-cons f g fg-inv) = fg-inv

[A≅B]→[gf≡id] : ∀ {α} {A : ★ α} {B : ★ α} ([A≅B] : A ≅ B) → ((a : A) → (([A≅B]→[B→A] [A≅B]) ∘ ([A≅B]→[A→B] [A≅B])) a ≡ a)
[A≅B]→[gf≡id] (≅-cons f g fg-inv) = ∧-π₁ fg-inv

[A≅B]→[fg≡id] : ∀ {α} {A : ★ α} {B : ★ α} ([A≅B] : A ≅ B) → ((b : B) → (([A≅B]→[A→B] [A≅B]) ∘ ([A≅B]→[B→A] [A≅B])) b ≡ b)
[A≅B]→[fg≡id] (≅-cons f g fg-inv) = ∧-π₂ fg-inv






structural-invariant : ∀ {α β} (P : ★ α → ★ β) → ★ ((lsuc α) ⊔ β)
structural-invariant {α} {β} P = (A B : ★ α) → A ≅ B → P A → P B

-- Is there any property that's not a structural invariant?
-- https://www.andrew.cmu.edu/user/awodey/preprints/siu.pdf
-- according to this, every property is structurally invariant
-- but is this a logical proof or a metalogical proof?



curry : ∀ {α β γ} {A : ★ α} {B : A → ★ β} {C : ( ∃ a ∈ A , (B a)) → ★ γ} → 
        ((p : ∃ a ∈ A , (B a)) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : 
 ∀ {α β γ} {A : ★ α} {B : A → ★ β} {C : ★ γ} → ((a : A) → (B a) → C) → (∃ a ∈ A , (B a)) → C
uncurry f (x , y) = f x y

true-iso : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
true-iso {α} {β} A B = ∃ f ∈ (A → B) , (∃ g ∈ (B → A) , ((g ∘ f ≡ id) ∧ (f ∘ g ≡ id)))

∘' :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} 
 (f : A → B) → (g : B → C) → A → C
∘' f g = g ∘ f



-- extensional equality of functions
FuncId : ∀ {α β} {A : ★ α} {B : ★ β} (f g : A → B) → ★ (α ⊔ β)
FuncId {α} {β} {A} {B} f g = (a : A) → f a ≡ g a



















-- Booleans

data 𝔹 : ★₀ where
 𝕥 : 𝔹
 𝕗 : 𝔹

poly-𝔹-F : ∀ {α} → Set α → Set α
poly-𝔹-F A = A → A → A

poly-𝔹 : ∀ {α} → Set (lsuc α)
poly-𝔹 {α} = {A : Set α} → poly-𝔹-F A

poly-𝕥 : ∀ {α} → poly-𝔹 { α }
poly-𝕥 {α} {A} t f = t

poly-𝕗 : ∀ {α} → poly-𝔹 { α }
poly-𝕗 {α} {A} t f = f

poly-𝔹-elim : ∀ {α} {A : Set α} → poly-𝔹 { α } → poly-𝔹-F A
poly-𝔹-elim {α} {A} b x y = b { A } x y




poly-𝔹-elim' : ∀ {α} (A : Set α) → (∀ {β} (B : Set β) → B → B → B) → A → A → A
poly-𝔹-elim' {α} A b x y = b { α } A x y

{-
upoly-𝔹-elim' =  ∀ {α} (A : Set α) → (∀ {β} (B : Set β) → B → B → B) → A → A → A
-}
upoly-𝔹-elim'' = ∀ {β} (B : Set β) → B → B → B

poly-∧-F : ∀ {α β γ} → Set α → Set β → Set γ → Set (γ ⊔ (α ⊔ β))
poly-∧-F {α} {β} {γ} A B C = (A → B → C) → C

poly-∧ : ∀ {α β γ} → Set α → Set β → Set ((lsuc γ) ⊔ (α ⊔ β))
poly-∧ {α} {β} {γ} A B = (C : Set γ) → poly-∧-F A B C

poly-∧-cons : ∀ {α β γ} → (A : Set α) → (B : Set β) → A → B → poly-∧ { α } { β } { γ } A B
poly-∧-cons {α} {β} {γ} A B a b C pair = pair a b

poly-∧-π₁ : ∀ {α β} → (A : Set α) → (B : Set β) → poly-∧ { α } { β } { α } A B → A
poly-∧-π₁ {α} {β} A B p = p A (λ x y → x)

poly-∧-π₂ : ∀ {α β} → (A : Set α) → (B : Set β) → poly-∧ { α } { β } { β } A B → B
poly-∧-π₂ {α} {β} A B p = p B (λ x y → y) 
{-
poly-∧-elim : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} → poly-∧-F A B C → poly-∧-F A B C
poly-∧-elim {α} {β} A B C p = 
-}
-- Take a Bool to the corresponding proposition:
𝔹-★ : 𝔹 → ★₀
𝔹-★ 𝕥 = ⊤
𝔹-★ 𝕗 = ⊥ 


{-
poly-𝔹-★ : poly-𝔹-F Set → Set
poly-𝔹-★ b = poly-𝔹-elim' Set b ⊤ ⊥
-}

{-
poly-𝔹-★ : ∀ {α} → poly-𝔹 { α } → Set
poly-𝔹-★ {α} b = poly-𝔹-elim' Set b ⊤ ⊥

[poly-𝔹-★-poly-𝕥≡𝔹-★-𝕥] : poly-𝔹-★ poly-𝕥 ≡ 𝔹-★ 𝕥
[poly-𝔹-★-poly-𝕥≡𝔹-★-𝕥] = ⟲ ⊤

[poly-𝔹-★-poly-𝕗≡𝔹-★-𝕗] : poly-𝔹-★ poly-𝕗 ≡ 𝔹-★ 𝕗
[poly-𝔹-★-poly-𝕗≡𝔹-★-𝕗] = ⟲ ⊥
-}
-- Boolean negation
! : 𝔹 → 𝔹
! 𝕥 = 𝕗
! 𝕗 = 𝕥


{-
poly-! : ∀ {α} → poly-𝔹-F (poly-𝔹 { α }) → poly-𝔹 { α }
poly-! {α} b = poly-𝔹-elim b (poly-𝕥 { α }) (poly-𝕗 { α }) 
-}

-- Boolean AND
_&&_ : 𝔹 → 𝔹 → 𝔹
_&&_ 𝕥 𝕥 = 𝕥
_&&_ 𝕥 𝕗 = 𝕗
_&&_ 𝕗 𝕥 = 𝕗
_&&_ 𝕗 𝕗 = 𝕗 

{-
poly-&& : ∀ {α} → poly-𝔹-F (poly-𝔹 { α }) → poly
-}

-- Boolean OR
_||_ : 𝔹 → 𝔹 → 𝔹
_||_ 𝕥 𝕥 = 𝕥
_||_ 𝕥 𝕗 = 𝕥
_||_ 𝕗 𝕥 = 𝕥
_||_ 𝕗 𝕗 = 𝕗


-- fun fact: this collection of Boolean functions is functionally complete
-- https://en.wikipedia.org/wiki/Functional_completeness

-- maybe we'll try to prove that later on


if_then_else_ : ∀ {α} {A : ★ α}  → 𝔹 → A → A → A
if 𝕥 then a1 else a2 = a1 
if 𝕗 then a1 else a2 = a2











-- The Peano naturals
data ℕ : ★₀ where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ

poly-ℕ-F : ∀ {α} → Set α → Set α
poly-ℕ-F A = A → (A → A) → A

poly-ℕ : ∀ {α} → Set (lsuc α)
poly-ℕ {α} = {A : Set α} → poly-ℕ-F A

poly-zero : ∀ {α} → poly-ℕ { α }
poly-zero {α} {A} z s = z

poly-suc : ∀ {α} → poly-ℕ { α } → poly-ℕ { α }
poly-suc {α} n = λ z s → s (n z s)

poly-ℕ-elim : ∀ {α} → {A : Set α} → poly-ℕ-F A → poly-ℕ-F A
poly-ℕ-elim {α} {A} n z s = n z s

-- Need to do this in order to use Arabic numerals as elements of ℕ.
-- It probably does more than that too, i.e. compiler optimizations
{-# BUILTIN NATURAL ℕ #-}


 


ℝ : ★₀
ℝ = ℕ → 𝔹



pred : ℕ → ℕ
pred 𝕫 = 𝕫
pred (𝕤 n) = n

poly-pred : ∀ {α} → poly-ℕ-F (poly-ℕ { α } ) → poly-ℕ { α }
poly-pred {α} n = poly-ℕ-elim n (poly-zero { α }) (poly-suc { α })










-- Algebraic structures:

--Latin squares:
LatinRight : ∀ {α} {A : ★ α} (• : A → A → A) → ★ α
LatinRight {α} {A} •' = ∀ (a b : A) → ∃! x ∈ A , (a • x ≡ b) 
 where 
  _•_ : A → A → A
  x • y = •' x y
  infix 2 _•_

LatinLeft : ∀ {α} {A : ★ α} (• : A → A → A) → ★ α
LatinLeft {α} {A} •' = ∀ (a b : A) → ∃! y ∈ A , (y • a ≡ b)
 where
  _•_ : A → A → A
  x • y = •' x y
  infix 2 _•_

LatinSquare : ∀ {α} {A : ★ α} (• : A → A → A) → ★ α
LatinSquare • = LatinLeft • ∧ LatinRight •



is-left-id : ∀ {α} {A : Set α} (+ : A → A → A) (e : A) → ★ α
is-left-id {α} {A} +' e = ∀ (a : A) → e + a ≡ a
 where
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_
  

is-right-id : ∀ {α} {A : ★ α} (+ : A → A → A) (e : A) → ★ α
is-right-id {α} {A} +' e = ∀ (a : A) → a + e ≡ a
 where
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_


--is a (given) object a universal identity for a binary operation
is-identity : ∀ {α} {A : ★ α} (+ : A → A → A) (e : A) → ★ α
is-identity {α} {A} +' e = ∀ (a : A) → e + a ≡ a ∧ a + e ≡ a
 where
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_



--does a (given) binary operation have a universal identity
has-identity : ∀ {α} {A : ★ α} (+ : A → A → A) → ★ α
has-identity {α} {A} + = ∃ e ∈ A , (is-identity + e)




record SemiMonoid : ★₁ where
 field
  M : ★₀
  + : M -> M -> M
  +-id : has-identity +





-- is a (given) binary operation associative
is-associative : ∀ {α} {A : ★ α} (+ : A → A → A) → ★ α
is-associative {α} {A} +' = ∀ {x y z : A} → (x + y) + z ≡ x + (y + z)
 where
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_

-- does a (given) SemiMonoid have left inverses
has-left-inverses : SemiMonoid → ★₀
has-left-inverses S = (x : M) → ∃ x⁻¹ ∈ M , (x⁻¹ * x ≡ e)

 where
  M : ★₀
  M = SemiMonoid.M S
  
  _*_ : M → M → M
  x * y = (SemiMonoid.+ S) x y
  infix 2 _*_

  e : M
  e = π₁ (SemiMonoid.+-id S)
  

-- does a (given) SemiMonoid have right inverses
has-right-inverses : SemiMonoid → ★₀
has-right-inverses S = (x : M) → ∃ x⁻¹ ∈ M , (x * x⁻¹ ≡ e)
 where
  M : ★₀
  M = SemiMonoid.M S

  _*_ : M → M → M
  x * y = (SemiMonoid.+ S) x y
  infix 2 _*_

  e : M
  e = π₁ (SemiMonoid.+-id S)

 
-- does a (given) SemiMonoid have both left & right inverses
has-inverses : SemiMonoid → ★₀
has-inverses S = (x : M) → has-left-inverses S ∧ has-right-inverses S
 where
  M : ★₀
  M = SemiMonoid.M S




-- is a (given) binary operation commutative
is-commutative : ∀ {α} {A : ★ α} (+ : A → A → A) → ★ α
is-commutative {α} {A} +' = (x y : A) → x + y ≡ y + x
 where
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_



-- does a given multiplication left-distribute over a given addition
left-distributive : ∀ {α} {A : ★ α} (* : A → A → A) → (+ : A → A → A) → ★ α
left-distributive {α} {A} *' +' = (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
 where
  _*_ : A → A → A
  x * y = *' x y
  infix 2 _*_
  
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_ 

-- does a given multiplication right-distribute over a given addition
right-distributive : ∀ {α} {A : ★ α} (* : A → A → A) → (+ : A → A → A) → ★ α
right-distributive {α} {A} *' +' = (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
 where
  _*_ : A → A → A
  x * y = *' x y
  infix 2 _*_

  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_


-- does a given multiplication distribute (generally) over a given addition
is-distributive : ∀ {α} {A : ★ α} (* : A → A → A) → (+ : A → A → A) → ★ α
is-distributive * + = (left-distributive * +) ∧ (right-distributive * +)


-- is a given algebraic structure a semigroup
is-semigroup : ∀ {α} {M : ★ α} (+ : M → M → M) → ★ α
is-semigroup + = is-associative +


-- is a given algebraic structure a monoid
is-monoid : ∀ {α} {M : ★ α} (+ : M → M → M) → ★ α
is-monoid + = (is-semigroup +) ∧ (has-identity +)


-- is a given algebraic structure a group
is-group : {M : ★₀} (+ : M → M → M) → ★₀
is-group {M} + = ∃ prf ∈ (is-monoid +) , (has-inverses (record {M = M; + = +; +-id = ∧-π₂ prf}))

-- is a given algebraic structure an Abelian group
is-abgroup : {M : ★₀} (+ : M → M → M) -> ★₀
is-abgroup + = (is-group +) ∧ (is-commutative +)


-- is a given algebraic structure a commutative monoid
is-commutative-monoid : ∀ {α} {M : ★ α} (+ : M → M → M) → ★ α
is-commutative-monoid + = (is-monoid +) ∧ (is-commutative +)


record Magma : ★₁ where
 field
  M : ★₀
  + : M → M → M


record QuasiGroup : ★₁ where
 field
  M : ★₀
  + : M -> M -> M
  +-sq : LatinSquare +


record Loop : ★₁ where
 field
  M : ★₀
  + : M → M → M
  +-sq : LatinSquare +
  +-id : has-identity + 



record SemiGroup : ★₁ where
 field
  M : ★₀
  + : M → M → M
  +-assoc : is-associative +


record Monoid : ★₁ where
 field
  M : ★₀
  + : M → M → M
  +-id : has-identity +
  +-assoc : is-associative +


record Group : Set (lsuc ℓ₁) where
 field
  M : ★₀
  + : M → M → M
  +-id : has-identity +
  +-assoc : is-associative +
  +-inv : has-inverses (record {M = M; + = +; +-id = +-id})


record AbelianGroup : Set (lsuc ℓ₁)  where
 field
  G : Group
  +-comm : is-commutative (Group.+ G) 


record rng : ★₁ where
 field
  M : ★₀
  + : M → M → M
  * : M → M → M
  +-abgroup : is-abgroup +
  *-semigroup : is-semigroup +
  *-dist : is-distributive * +


record Ring : ★₁ where
 field
  M : ★₀
  + : M → M → M
  * : M → M → M
  +-abgroup : is-abgroup +
  *-monoid : is-monoid *
  *-dist : is-distributive * +


record CommutativeMonoid : ★₁ where
 field
  M : Set
  + : M → M → M
  +-id : has-identity +
  +-assoc : is-associative +
  +-comm : is-commutative +





















-- addition on Nats
_+_ : ℕ → ℕ → ℕ
0 + y = y
(𝕤 x) + y = 𝕤 (x + y)
infixr 2 _+_

_+'_ : ℕ → ℕ → ℕ
x +' y = y + x
infix 2 _+'_


--This attempt just returns m
_minus_ : ℕ → ℕ → ℕ
0 minus n = 0
(𝕤 m) minus n = 𝕤 (m minus n)
infix 2 _minus_

diff : ℕ → ℕ → ℕ
diff 0 x = x
diff x 0 = x
diff (𝕤 x) (𝕤 y) = diff x y



isZero : ℕ → 𝔹
isZero 0 = 𝕥
isZero (𝕤 x) = 𝕗


_*_ : ℕ → ℕ → ℕ
0 * y = 0 
(𝕤 x) * y = y + (x * y) 
infix 3 _*_


_*'_ : ℕ → ℕ → ℕ
x *' y = y * x
infix 3 _*'_


_^_ : ℕ → ℕ → ℕ
x ^ 0 = 1
x ^ (𝕤 y) = x * (x ^ y)
infix 4 _^_

_^'_ : ℕ → ℕ → ℕ
x ^' y = y ^ x
infix 4 _^'_

_gte_ : ℕ → ℕ → 𝔹
0 gte 0 = 𝕥
0 gte (𝕤 n) = 𝕗
(𝕤 n) gte 0 = 𝕥
(𝕤 n) gte (𝕤 m) = n gte m
infix 2 _gte_ 





even : ℕ → 𝔹
even 0 = 𝕥
even 1 = 𝕗
even (𝕤 (𝕤 n)) = even n

odd : ℕ → 𝔹
odd 0 = 𝕗
odd 1 = 𝕥
odd (𝕤 (𝕤 n)) = odd n

Even : (x : ℕ) → ★₀
Even x = ∃ k ∈ ℕ , (x ≡ 2 * k)

Odd : (x : ℕ) → ★₀
Odd x = ∃ k ∈ ℕ , (x ≡ 2 * k + 1)




{-
dependencies:
  _+_ : ℕ → ℕ → ℕ
-}
_≥_ : ℕ → ℕ → ★₀
x ≥ y = ∃ n ∈ ℕ , (y + n ≡ x)
infix 1 _≥_ 

_≱_ : ℕ → ℕ → ★₀
x ≱ y =  ¬ (x ≥ y)
infix 1 _≱_

_>_ : ℕ → ℕ → ★₀
x > y = ∃ n ∈ ℕ , (∃ m ∈ ℕ , (𝕤 m ≡ n ∧ y + n ≡ x))
infix 1 _>_

_≯_ : ℕ → ℕ → ★₀
x ≯ y = ¬ (x > y)
infix 1 _≯_

_≤_ : ℕ → ℕ → ★₀
x ≤ y = y ≥ x
infix 1 _≤_

_≰_ : ℕ → ℕ → ★₀
x ≰ y = y ≱ x
infix 1 _≰_

_<_ : ℕ → ℕ → ★₀
x < y = y > x
infix 1 _<_

_≮_ : ℕ → ℕ → ★₀
x ≮ y = y ≯ x
infix 1 _≮_



data ℕ* : ★₀ where
 ℕ*-cons : (x : ℕ) → x > 0 → ℕ*


-- Integers : 
data ℤ : ★₀ where
 ℤ-0 : ℤ
 pos : ℕ* → ℤ
 neg : ℕ* → ℤ

data ℤ* : ★₀ where
 ℤ*-cons : (x : ℤ) → x ≠ ℤ-0 → ℤ*

data ℚ+ : ★₀ where
 +<_>/_ : ℕ → ℕ* → ℚ+
infix 3 _/_

ℚ+-num : ℚ+ → ℕ
ℚ+-num (+< x >/ y) = x

ℚ+-den : ℚ+ → ℕ*
ℚ+-den (+< x >/ y) = y

data ℚ+* : ★₀ where
 ℚ+*-cons : ℕ* → ℕ* → ℚ+* 

data ℚ : ★₀ where
 _/_ : ℤ → ℕ* → ℚ

numerator : ℚ → ℤ
numerator (x / y) = x

denominator : ℚ → ℕ*
denominator (x / y) = y

ℕ*→ℕ : ℕ* → ℕ
ℕ*→ℕ (ℕ*-cons n [n>0]) = n
{-
ℤ-+ : ℤ → ℤ → ℤ
ℤ-+ = 

_÷_ : ℚ → ℚ → ℚ
(a / b) ÷ (c / d) = ((a * d) /( b * c))

-}



{-
_%_ : ℕ → ℕ* → ℕ
x % y = if ((ℕ*→ℕ y) gte (𝕤 x)) then x else (if (x gte (ℕ*→ℕ y)) then ((x minus (ℕ*→ℕ y)) % y) else 0)
-}

{-
data Acc (n : ℕ) : ★₀ where
 acc : (∀ m → m < n → Acc m) → Acc n

WF : Set
WF = ∀ (n : ℕ) → Acc n
-}



data Maybe {α} (A : ★ α) : ★ α where
 Just : (a : A) → Maybe A  
 Nothing : Maybe A


 

-- Homogeneous binary relations : 
{-
  Should probably make heterogeneous n-ary relations instead and define
  homogeneous binary relations as a special case.
-}


relation : ∀ {α} {A : ★ α} → ★ α
relation {α} {A} = A → A → 𝔹


--Reflexivity
IsReflexive : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsReflexive {α} {A} R' = (a : A) → a R a ≡ 𝕥
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_
 

IsIrreflexive : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsIrreflexive {α} {A} R' = (a : A) -> a R a ≡ 𝕗
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_



--Symmetry
IsSymmetric : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsSymmetric {α} {A} R' = (a b : A) → a R b ≡ 𝕥 → b R a ≡ 𝕥
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_


IsAntisymmetric : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsAntisymmetric {α} {A} R' = (a b : A) → (a R b ≡ 𝕥) → (b R a ≡ 𝕥) → (a ≡ b)
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_


IsAsymmetric : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsAsymmetric {α} {A} R' = (a b : A) → (a R b ≡ 𝕥) → (b R a ≡ 𝕗)
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_


--Transitivity
IsTransitive : ∀ {α} {A : ★ α} → relation { α } { A } -> ★ α
IsTransitive {α} {A} R' = (a b c : A) → (a R b ≡ 𝕥) → (b R c ≡ 𝕥) → (a R c ≡ 𝕥)
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_




--Specific relations
IsPreorder : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsPreorder {α} {A} R = (IsReflexive R) ∧ (IsTransitive R)

IsPartialOrder : ∀ {α} {A : ★ α} → relation { α } { A } → ★ α
IsPartialOrder {α} {A} R = (IsReflexive R) ∧ (IsAntisymmetric R) ∧ (IsTransitive R)

IsEquivalence : ∀ {α} {A : ★ α} → relation { α } { A } -> ★ α
IsEquivalence {α} {A} R = (IsReflexive R) ∧ (IsSymmetric R) ∧ (IsTransitive R)



--These definitions have to return universe-polymorphic function types
--which means their return type is actually not Set (lmax m n), but SetOmega
--which is not allowed in Agda.
--Why?
{-
epimorphic : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
epimorphic {m} {n} {A} {B} f = 
 {q : Level} {C : Set q} (g1 g2 : B -> C) -> FuncId (comp g1 f) (comp g2 f) -> FuncId g1 g2

epimorphic-strong : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
epimorphic-strong {m} {n} {A} {B} f = 
 {q : Level} {C : Set q} (g1 g2 : B -> C) -> Id (comp g1 f) (comp g2 f) -> Id g1 g2

monomorphic : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
monomorphic {m} {n} {A} {B} f =
 {q : Level} {C : Set q} (g1 g2 : C -> A) -> FuncId (comp f g1) (comp f g2) -> FuncId g1 g2

monomorphic-strong : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
monomorphic-strong {m} {n} {A} {B} f = 
 {q : Level} {C : Set q} (g1 g2 : C -> A) -> Id (comp f g1) (comp f g2) -> Id g1 g2

-}  

-- needs more defining axioms in order to actually characterizie it as a Functor
record Functor {α β} {A : ★ α} {B : ★ β} : ★ (α ⊔ β) where
 field
  omap : A → B
  fmap : (A → A) → (B → B)
  
data [_] {α} (A : ★ α) : ★ α where
 [] : [ A ]
 _::_ : A → [ A ] → [ A ]

list-length : ∀ {α} {A : ★ α} → (l : [ A ]) → ℕ
list-length [] = 0
list-length (first :: rest) = 𝕤 (list-length rest) 

maybe-list-first : ∀ {α} {A : ★ α} → (l : [ A ]) → Maybe A
maybe-list-first [] = Nothing
maybe-list-first (first :: rest ) = Just first

maybe-list-rest : ∀ {α} {A : ★ α} → (l : [ A ]) → Maybe ([ A ])
maybe-list-rest [] = Nothing
maybe-list-rest (first :: rest) = Just rest

maybe-list-last : ∀ {α} {A : ★ α} → (l : [ A ]) → Maybe A
maybe-list-last [] = Nothing
maybe-list-last (first :: []) = Just first
maybe-list-last (first :: (second :: rest)) = maybe-list-last (second :: rest)


maybe-list-idx-n : ∀ {α} {A : ★ α} → (l : [ A ]) → ℕ → Maybe A
maybe-list-idx-n [] n = Nothing
maybe-list-idx-n (first :: rest) 0 = Just first
maybe-list-idx-n (first :: rest) (𝕤 n) = maybe-list-idx-n rest n

list-add-to-end : ∀ {α} {A : ★ α} → (l : [ A ]) → A → [ A ]
list-add-to-end [] a = (a :: [])
list-add-to-end (first :: rest) a = (first :: (list-add-to-end rest a))

list-reverse : ∀ {α} {A : ★ α} → (l : [ A ]) → [ A ]
list-reverse [] = []
list-reverse {α} {A} (first :: rest) = list-add-to-end rest first

_++_ : ∀ {α} {A : ★ α} → (l1 l2 : [ A ]) → [ A ]
[]         ++ []         =  []
(f1 :: r1) ++ []         = (f1 :: r1)
[]         ++ (f2 :: r2) = (f2 :: r2)
(f1 :: r1) ++ (f2 :: r2) = (list-add-to-end (f1 :: r1) f2) ++ r2

list-rotate-l : ∀ {α} {A : ★ α} → (l : [ A ]) → [ A ]
list-rotate-l [] = []
list-rotate-l (f :: r) = list-add-to-end r f

list-rotate-r : ∀ {α} {A : ★ α} → (l : [ A ]) → [ A ] → [ A ]
list-rotate-r [] acc = []
list-rotate-r (f :: []) acc = (f :: acc)
list-rotate-r (f :: (s :: r)) acc = list-rotate-r (s :: r) (acc ++ (f :: []))

list-map : ∀ {α β} {A : ★ α} {B : ★ β} → (F : A → B) → (l : [ A ]) → [ B ]
list-map {α} {β} {A} {B} F [] = []
list-map {α} {β} {A} {B} F (f :: r) = ((F f) :: (list-map F r))

list-fold : ∀ {α β} {A : ★ α} {B : ★ β} → (F : A → B → B) → B → [ A ] → B 
list-fold {α} {β} {A} {B} F acc [] = acc
list-fold {α} {β} {A} {B} F acc (f :: r) = list-fold F (F f acc) r 






data Vec {α} (A : ★ α) : ℕ → ★ α where
 Vec-nil : Vec A 0
 Vec-cons : {n : ℕ} → A → Vec A n → Vec A (𝕤 n)

data BinTree {α} (A : ★ α) : ★ α where
 Tree-nil : BinTree A
 Node : A → BinTree A → BinTree A → BinTree A
 
tree-map : ∀ {α β} {A : ★ α} {B : ★ β} → (F : A → B) → (treeA : BinTree A) → BinTree B
tree-map {α} {β} {A} {B} F Tree-nil = Tree-nil
tree-map {α} {β} {A} {B} F (Node a branch-l branch-r) = Node (F a) (tree-map F branch-l) (tree-map F branch-r)

AdjList : ∀ {α} (A : ★ α) → ★ α
AdjList {α} A = [ A ] ∧ [ A ∧ A ]

AdjMatrix : ∀ {α} (A : ★ α) → ★ α
AdjMatrix {α} A = A ∧ A → 𝔹

data Ord : ★₀ where
 zeroOrd : Ord
 sucOrd : Ord → Ord
 limOrd : (ℕ → Ord) → Ord


{-
 Everything before this point is definitions
 Everything after is theorems

-}

data Term : ★₀ where
 Const : ℕ → Term
 Mult : Term → Term → Term

{-
eval : Term → ℕ
eval (Const a) = a
eval (Mult a b) = a * b
-}
































-- Basic implications:

-- True implies True
⊤→⊤ : ⊤ → ⊤
⊤→⊤ = id

⊤→⊤₂ : ⊤ → ⊤
⊤→⊤₂ ● = ●


-- False implies False
⊥→⊥ : ⊥ → ⊥
⊥→⊥ = id

-- False implies True
⊥→⊤ : ⊥ → ⊤
⊥→⊤ ☢ = ω ☢

-- True doesn't imply False
¬[⊤→⊥] : (⊤ → ⊥) → ⊥
¬[⊤→⊥] [⊤→⊥] = [⊤→⊥] ●







-- ¬(A∨B) implies ¬(A∧B)  
[¬[A∨B]]→[¬[A∧B]] : ∀ {α β} (A : ★ α) (B : ★ β) → (¬ (A ∨ B) → ¬ (A ∧ B))
[¬[A∨B]]→[¬[A∧B]] A B [¬∨] (∧-cons x y) = [¬∨] (∨-cons1 x)

-- (A∧B) implies (A∨B)
[A∧B]→[A∨B] : ∀ {α β} {A : ★ α} {B : ★ β} → (A ∧ B → A ∨ B)
[A∧B]→[A∨B] {A} {B} (∧-cons x y) = ∨-cons1 x  

[A∧B]→[A∨B]₂ : ∀ {α β} {A : ★ α} {B : ★ β} → (A ∧ B → A ∨ B)
[A∧B]→[A∨B]₂ {A} {B} (∧-cons x y) = ∨-cons2 y








-- If A = B then A → B
[A=B]→[A→B] : ∀ {α} {A B : ★ α} (p : A ≡ B) → (A → B)
[A=B]→[A→B] {α} {A} {.A} (⟲ .A) x = x


-- thus, ⊤ is not equal to ⊥ 
⊤≠⊥ : ⊤ ≠ ⊥
⊤≠⊥ p = [A=B]→[A→B] p ●



-- Equality is reflexive
≡-⟲ : ∀ {α} {A : ★ α} (x : A) → x ≡ x
≡-⟲ = ⟲


-- Equality is symmetric
≡-↑↓ : ∀ {α} {A : ★ α} {x y : A} (p : x ≡ y) → y ≡ x
≡-↑↓ (⟲ a) = ⟲ a


-- Equality is transitive
≡-⇶ : ∀ {α} {A : ★ α} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
≡-⇶ (⟲ x) (⟲ .x) = ⟲ x

≡-⇶₂ : ∀ {α} {A : ★ α} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
≡-⇶₂ (⟲ x) e = e


≠-irreflexive : ∀ {α} {A : ★ α} (x : A) → x ≠ x → ⊥
≠-irreflexive x [x≠x] = [x≠x] (⟲ x)

≠-↑↓ : ∀ {α} {A : ★ α} {x y : A} → x ≠ y → y ≠ x
≠-↑↓ [x≠y] [y≡x] = ☢
 where
  ☢ : ⊥
  ☢ = [x≠y] (≡-↑↓ [y≡x])


-- Path transport
Δ : ∀ {α β} {A : ★ α} {x y : A} (p : x ≡ y) (P : A → ★ β) → P x → P y
Δ {α} {β} {A} {a} {.a} (⟲ .a) P pa = pa

-- Propositional transport
★-Δ : ∀ {α β} (A : ★ α) (B : ★ α) (p : A ≡ B) (P : A → ★ β) → (B → ★ β)
★-Δ A .A (⟲ .A) [A→★] = [A→★]


-- Functions preserve equality
[a≡b]→[fa≡fb] : 
 ∀ {α β} {A : ★ α} {B : ★ β} 
 (f : A → B) (x y : A) (p : x ≡ y) → 
 f x ≡ f y
[a≡b]→[fa≡fb] f a .a (⟲ .a) = ⟲ (f a) 

-- PI's preserve equality
[a≡b]→[Pa≡Pb] : 
 ∀ {α β} {A : ★ α} {B : A → ★ β} 
 (f : (a : A) → B a) (x y : A) (p : x ≡ y) → 
 Δ p B (f x) ≡ f y
[a≡b]→[Pa≡Pb] f a .a (⟲ .a) = ⟲ (f a)


-- Isomorphism is reflexive
≅-⟲ : ∀ {α} (A : ★ α) → A ≅ A
≅-⟲ A = ≅-cons id id (∧-cons (λ a → ⟲ a) (λ b → ⟲ b))

-- Isomorphism is symmetric
≅-↑↓ : ∀ {α} (A B : ★ α) → A ≅ B → B ≅ A
≅-↑↓ A B (≅-cons f g fg-inv) = ≅-cons g f (∧-cons (∧-π₂ fg-inv) (∧-π₁ fg-inv))

-- Isomorphism is transitive
≅-⇶ : ∀ {α} (A B C : ★ α) → A ≅ B → B ≅ C → A ≅ C
≅-⇶ A B C [A≅B] [B≅C] = ≅-cons (h ∘ f) (g ∘ i) (∧-cons gi-inv-hf hf-inv-gi)
 where
  f : A → B
  f = [A≅B]→[A→B] [A≅B]

  g : B → A
  g = [A≅B]→[B→A] [A≅B]

  h : B → C
  h = [A≅B]→[A→B] [B≅C]
 
  i : C → B
  i = [A≅B]→[B→A] [B≅C]
  
  [ih≡id] : (b : B) → (i ∘ h) b ≡ b
  [ih≡id] = [A≅B]→[gf≡id] [B≅C]

  [hi≡id] : (c : C) → (h ∘ i) c ≡ c
  [hi≡id] = [A≅B]→[fg≡id] [B≅C]

  [fg≡id] : (b : B) → (f ∘ g) b ≡ b
  [fg≡id] = [A≅B]→[fg≡id] [A≅B] 

  [gf≡id] : (a : A) → (g ∘ f) a ≡ a
  [gf≡id] = [A≅B]→[gf≡id] [A≅B]

  [ihfa≡fa] : (a : A) → i (h (f a)) ≡ f a
  [ihfa≡fa] a = [ih≡id] (f a)

  [gihfa≡gfa] : (a : A) → g (i (h (f a))) ≡ g (f a)
  [gihfa≡gfa] a = [a≡b]→[fa≡fb] g (i (h (f a))) (f a) ([ihfa≡fa] a)

  gi-inv-hf : (a : A) → g (i (h (f a))) ≡ a
  gi-inv-hf a = ≡-⇶ ([gihfa≡gfa] a) ([gf≡id] a)

  [fgic≡ic] : (c : C) → f (g (i c)) ≡ i c
  [fgic≡ic] c = [fg≡id] (i c)

  [hfgic≡hic] : (c : C) → h (f (g (i c))) ≡ h (i c)
  [hfgic≡hic] c = [a≡b]→[fa≡fb] h (f (g (i c))) (i c) ([fgic≡ic] c)

  hf-inv-gi : (c : C) → h (f (g (i c))) ≡ c
  hf-inv-gi c = ≡-⇶ ([hfgic≡hic] c) ([hi≡id] c)




--principle of invariance implies univalence
POI→UA : ∀ {α} (A B : ★ α) → (∀ {γ δ} (P : ★ γ → ★ δ) (C D : ★ γ) → C ≅ D → P C → P D) → (A ≅ B → A ≡ B)
POI→UA A B SIP [A≅B] = SIP (λ T → A ≡ T) A B [A≅B] (⟲ A)

--univalence implies principle of invariance  
UA→POI : (∀ {α} (A B : ★ α) → (A ≅ B → A ≡ B)) → (∀ {γ δ} (P : ★ γ → ★ δ) (C D : ★ γ) → (C ≅ D) → P C → P D)
UA→POI UA P C D [C≅D] PC = Δ (UA C D [C≅D]) P PC

--univalence implies function-extensionality ?
{-
UA→FE : (∀ {α} (A B : ★ α) → (A ≅ B → A ≡ B)) → (∀ {γ δ} (C : ★ γ) (D : ★ δ) (f g : C → D) → ((x : C) → f x ≡ g x) → f ≡ g)
UA→FE UA C D f g fg-ext-id = 

-}

--Angiuli, Harper, Wilson
--Computational Higher Type Theory

--Coquand, Mortberg, Huber
--https://www.math.ias.edu/~amortberg/papers/cubicaltt.pdf
--https://arxiv.org/pdf/1607.04156v1.pdf

--Adam, Bezem, Coquand
--https://arxiv.org/abs/1610.00026


--Licata, Brunerie
--http://dlicata.web.wesleyan.edu/pubs/lb15cubicalsynth/lb15cubicalsynth.pdf

--Awodey slides
--http://www.helsinki.fi/lc2015/materials/slides_awodey.pdf

--https://github.com/HoTT/HoTT

--Voevodsky's conjecture: there is a procedure for normalization "up to homotopy"



≅-Δ :
 -- for every pair A, B of isomorphic sets
 ∀ {α β} (A B : ★ α) ([A≅B] : A ≅ B)
 -- and every proposition P defined on A
 (P : A → ★ β)
 -- an object from A and an object from B 
 (a : A) (b : B) →
 let f = ≅-π₁ [A≅B] in
  let g = ≅-π₂ [A≅B] in
   (f a ≡ b) → P a → (P ∘ g) b
 
≅-Δ A B [A≅B] P a b [fa≡b] Pa = Δ [a≡gb] P Pa    
 where
  f : A → B
  f = ≅-π₁ [A≅B]
  
  g : B → A
  g = ≅-π₂ [A≅B]

  a→[gfa≡a] : (a : A) → _≡_ ((g ∘ f) a) a
  a→[gfa≡a] = ∧-π₁ (≅-π₃ [A≅B])

  [a≡gfa] : _≡_ a ((g ∘ f) a)
  [a≡gfa] = ≡-↑↓ (a→[gfa≡a] a) 

  [gfa≡gb] : _≡_ ((g ∘ f) a) (g b)
  [gfa≡gb] = [a≡b]→[fa≡fb] g (f a) b [fa≡b]
  
  [a≡gb] : _≡_ a (g b)
  [a≡gb] = ≡-⇶ [a≡gfa] [gfa≡gb]
  
{-
    [a≡gb]
    /     \
   /       \
   [a≡gfa≡gb]
     |   |
   [A≅B] |g∘
         |
      [fa≡b]
-}


-- Boolean true is not equal to Boolean false
𝕥≠𝕗 : 𝕥 ≠ 𝕗
𝕥≠𝕗 p = ⊤≠⊥ ([a≡b]→[fa≡fb] 𝔹-★ 𝕥 𝕗 p)

𝕗≠𝕥 : 𝕗 ≠ 𝕥
𝕗≠𝕥 = ≠-↑↓ 𝕥≠𝕗


-- No Boolean equals its own negation
a≠!a : ∀ (a : 𝔹) → a ≠ ! a
a≠!a 𝕥 p = 𝕥≠𝕗 p
a≠!a 𝕗 p = 𝕗≠𝕥 p










-- equal functions on equal arguments have equal results:
[f≡g]→[fa≡ga] : 
  ∀ {α β} {A : ★ α} {B : ★ β} →
  (f g : A → B) → (h : f ≡ g) → (a : A) → 
  f a ≡ g a
[f≡g]→[fa≡ga] {α} {β} {A} {B} f .f (⟲ .f) a = ⟲ (f a)

[f≡g]→[fa≡ga]₂ : 
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f g : A → B) → (h : f ≡ g) → (a1 a2 : A) → a1 ≡ a2 → 
 f a1 ≡ g a2
[f≡g]→[fa≡ga]₂ {α} {β} {A} {B} f .f (⟲ .f) a .a (⟲ .a) = ⟲ (f a)




-- SECTION : Successor and addition
-- 1)  𝕫 is not the successor of any number
-- 2)  𝕤 is an injection
-- 3)  pred 𝕤n ≡ n
-- 4)  𝕤x≠x : x is not equal to its successor
-- 5)  𝕫 + x ≡ x
-- 6)  x + 𝕫 ≡ x
-- 7)  𝕤𝕫 + x = 𝕤x
-- 8)  𝕤x + y ≡ 𝕤(x + y)
-- 9)  x + 𝕤𝕫 ≡ 𝕤x
-- 10) 𝕤(x + y) ≡ x + 𝕤y
-- 11) [a+x]+y ≡ x+[a+y]
-- 12) Addition is commutative
-- 13) Addition is associative 
-- 14) 𝕫 is a unique right identity for (ℕ,+)
-- 15) 𝕫 is a unique left identity for (ℕ,+)
-- 16) If x + y ≡ 0 then x ≡ 0 and y ≡ 0


-- 1) 𝕫 is not the successor of any number
𝕤x≠𝕫 : (x : ℕ) → (𝕤 x) ≠ 𝕫
𝕤x≠𝕫 x [𝕤x≡𝕫] = ☢
 where
  [𝕥≡isZero-𝕫] : 𝕥 ≡ isZero 𝕫
  [𝕥≡isZero-𝕫] = ⟲ 𝕥

  [isZero-𝕤x≡𝕗] : isZero (𝕤 x) ≡ 𝕗
  [isZero-𝕤x≡𝕗] = ⟲ 𝕗

  [isZero-𝕫≡isZero-𝕤x] : isZero 𝕫 ≡ isZero (𝕤 x)
  [isZero-𝕫≡isZero-𝕤x] = [f≡g]→[fa≡ga]₂ isZero isZero (⟲ isZero) 𝕫 (𝕤 x) (≡-↑↓ [𝕤x≡𝕫])

  [𝕥≡𝕗] : 𝕥 ≡ 𝕗
  [𝕥≡𝕗] = ≡-⇶ (≡-⇶ [𝕥≡isZero-𝕫] [isZero-𝕫≡isZero-𝕤x]) [isZero-𝕤x≡𝕗]

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
{-
               ☢
               ^
               |
              𝕥≠𝕗
               |
             [𝕥≡𝕗]
         /          \
  [𝕥 ≡ isZero-𝕫 ≡ isZero-𝕤x ≡ 𝕗]
     ^          ^             ^
     |          |             |
  def:isZero-𝕫  |isZero     def:isZero-𝕤x
                |
             [𝕫≡𝕤x]
-}


𝕫≠𝕤x : (x : ℕ) → 𝕫 ≠ (𝕤 x)
𝕫≠𝕤x x = ≠-↑↓ (𝕤x≠𝕫 x)






-- 2) 𝕤 is an injection:
[𝕤x≡𝕤y]→[x≡y] : (x y : ℕ) → (𝕤 x) ≡ (𝕤 y) → x ≡ y
[𝕤x≡𝕤y]→[x≡y] x y [𝕤x≡𝕤y] = [a≡b]→[fa≡fb] pred (𝕤 x) (𝕤 y) [𝕤x≡𝕤y]




-- 3) pred 𝕤n ≡ n
pred-𝕤n≡n : (n : ℕ) → pred (𝕤 n) ≡ n
pred-𝕤n≡n n = ⟲ n




-- 4) 𝕤x≠x  :  x is not equal to its successor

-- base case for 𝕤x≠x
𝕤𝕫≠𝕫 : (𝕤 𝕫) ≠ 𝕫
𝕤𝕫≠𝕫 [𝕤𝕫≡𝕫] = ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 ([f≡g]→[fa≡ga]₂ even even (⟲ even) 𝕫 (𝕤 𝕫) (≡-↑↓ [𝕤𝕫≡𝕫]))


-- inductive step for 𝕤x≠x
[𝕤x≠x]→[𝕤𝕤x≠𝕤x] : (x : ℕ) → (𝕤 x) ≠ x → (𝕤 (𝕤 x)) ≠ (𝕤 x)
[𝕤x≠x]→[𝕤𝕤x≠𝕤x] x [𝕤x≠x] [𝕤𝕤x≡𝕤x] = ☢
 where
  ☢ : ⊥
  ☢ = [𝕤x≠x] ([a≡b]→[fa≡fb] pred (𝕤 (𝕤 x)) (𝕤 x) [𝕤𝕤x≡𝕤x])

-- final step for 𝕤x≠x
𝕤x≠x : (x : ℕ) → (𝕤 x) ≠ x
𝕤x≠x 𝕫 = 𝕤𝕫≠𝕫
𝕤x≠x (𝕤 x) = [𝕤x≠x]→[𝕤𝕤x≠𝕤x] x (𝕤x≠x x)

x≠𝕤x : (x : ℕ) → x ≠ (𝕤 x)
x≠𝕤x x = ≠-↑↓ (𝕤x≠x x)



-- 5) 𝕫 + x ≡ x
𝕫+x≡x : (x : ℕ) → 𝕫 + x ≡ x
𝕫+x≡x x = ⟲ x

x≡𝕫+x : (x : ℕ) → x ≡ 𝕫 + x
x≡𝕫+x x = ≡-↑↓ (𝕫+x≡x x)



-- 6) x + 𝕫 ≡ x

-- base case for x + 𝕫 ≡ x
𝕫+𝕫≡𝕫 : 𝕫 + 𝕫 ≡ 𝕫
𝕫+𝕫≡𝕫 = ⟲ 𝕫
 
-- inductive step for x + 𝕫 ≡ x
[x+𝕫≡x]→[𝕤x+𝕫≡𝕤x] : (x : ℕ) → (x + 𝕫 ≡ x) → (𝕤 x + 𝕫 ≡ 𝕤 x)
[x+𝕫≡x]→[𝕤x+𝕫≡𝕤x] x [x+𝕫≡x] = [a≡b]→[fa≡fb] 𝕤 (x + 𝕫) x [x+𝕫≡x] 

x+𝕫≡x : (x : ℕ) → x + 𝕫 ≡ x
x+𝕫≡x 𝕫 = 𝕫+𝕫≡𝕫
x+𝕫≡x (𝕤 x) = [x+𝕫≡x]→[𝕤x+𝕫≡𝕤x] x (x+𝕫≡x x)

x≡x+𝕫 : (x : ℕ) → x ≡ x + 𝕫
x≡x+𝕫 x = ≡-↑↓ (x+𝕫≡x x)






-- 7) 𝕤z + x ≡ 𝕤x
𝕤𝕫+x≡𝕤x : (x : ℕ) → (𝕤 𝕫) + x ≡ 𝕤 x
𝕤𝕫+x≡𝕤x x = ⟲ (𝕤 x)







-- 8) (𝕤 x) + y ≡ 𝕤 (x + y)
𝕤x+y≡𝕤[x+y] : (x y : ℕ) → (𝕤 x) + y ≡ 𝕤 (x + y)
𝕤x+y≡𝕤[x+y] x y = ⟲ (𝕤 (x + y))

𝕤[x+y]≡𝕤x+y : (x y : ℕ) → (𝕤 (x + y)) ≡ (𝕤 x) + y
𝕤[x+y]≡𝕤x+y x y = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x y)








-- 9) x + (𝕤 𝕫) ≡ (𝕤 x)

-- base case for x+𝕤𝕫≡𝕤x

𝕫+𝕤𝕫≡𝕤𝕫 : 𝕫 + (𝕤 𝕫) ≡ (𝕤 𝕫)
𝕫+𝕤𝕫≡𝕤𝕫 = ⟲ (𝕤 𝕫)


-- inductive step for x+𝕤𝕫≡𝕤x
[x+𝕤𝕫≡𝕤x]→[𝕤x+𝕤𝕫≡𝕤𝕤x] : (x : ℕ) → x + (𝕤 𝕫) ≡ 𝕤 x → (𝕤 x) + (𝕤 𝕫) ≡ 𝕤 (𝕤 x)
[x+𝕤𝕫≡𝕤x]→[𝕤x+𝕤𝕫≡𝕤𝕤x] x [x+𝕤𝕫≡𝕤x] = [𝕤x+𝕤𝕫≡𝕤𝕤x]
 where
-- a)
  [𝕤x+𝕤𝕫≡𝕤[x+𝕤𝕫]] : (𝕤 x) + (𝕤 𝕫) ≡ 𝕤 (x + (𝕤 𝕫))
  [𝕤x+𝕤𝕫≡𝕤[x+𝕤𝕫]] = 𝕤x+y≡𝕤[x+y] x (𝕤 𝕫)

-- b)
  [𝕤[x+𝕤𝕫]≡𝕤𝕤x] : 𝕤 (x + 𝕤 𝕫) ≡ 𝕤 (𝕤 x)
  [𝕤[x+𝕤𝕫]≡𝕤𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (x + 𝕤 𝕫) (𝕤 x) [x+𝕤𝕫≡𝕤x] 

-- Goal:
  [𝕤x+𝕤𝕫≡𝕤𝕤x] : (𝕤 x) + (𝕤 𝕫) ≡ 𝕤 (𝕤 x)
  [𝕤x+𝕤𝕫≡𝕤𝕤x] = ≡-⇶ [𝕤x+𝕤𝕫≡𝕤[x+𝕤𝕫]] [𝕤[x+𝕤𝕫]≡𝕤𝕤x]
{-
         [𝕤x+𝕤𝕫≡𝕤𝕤x]
   ____________|___________
   |                       |
          a)         b)
   [𝕤x+𝕤𝕫 ≡ 𝕤[x+𝕤𝕫] ≡ 𝕤𝕤x]
          ^          ^
          |          |𝕤
          |      [x+𝕤𝕫≡𝕤x] -- ind. hyp. 
      𝕤x+y≡𝕤[x+y]
          /\
         x  𝕤𝕫
-}

-- final step for x+𝕤𝕫≡𝕤x
x+𝕤𝕫≡𝕤x : (x : ℕ) → x + (𝕤 𝕫) ≡ 𝕤 x
x+𝕤𝕫≡𝕤x 𝕫 = 𝕫+𝕤𝕫≡𝕤𝕫
x+𝕤𝕫≡𝕤x (𝕤 n) = [x+𝕤𝕫≡𝕤x]→[𝕤x+𝕤𝕫≡𝕤𝕤x] n (x+𝕤𝕫≡𝕤x n)

𝕤x≡x+𝕤𝕫 : (x : ℕ) → (𝕤 x) ≡ x + (𝕤 𝕫)
𝕤x≡x+𝕤𝕫 x = ≡-↑↓ (x+𝕤𝕫≡𝕤x x)







-- 10) 𝕤 (x + y) ≡ x + (𝕤 y)


-- Base case for 𝕤[x+y]≡x+𝕤y
𝕤[𝕫+y]≡𝕫+𝕤y : (y : ℕ) → 𝕤 (𝕫 + y) ≡ 𝕫 + (𝕤 y)
𝕤[𝕫+y]≡𝕫+𝕤y y = ⟲ (𝕤 y)


-- Inductive step for 𝕤[x+y]≡x+𝕤y
[𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y] :
 (x y : ℕ) → 
 (𝕤 (x + y)) ≡ x + (𝕤 y) →
 (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
[𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y] x y [𝕤[x+y]≡x+𝕤y] = [𝕤[𝕤x+y]≡𝕤x+𝕤y] 
 where

-- a)
   [𝕤x+y≡𝕤[x+y]] : (𝕤 x) + y ≡ (𝕤 (x + y))
   [𝕤x+y≡𝕤[x+y]] = 𝕤x+y≡𝕤[x+y] x y

   [𝕤x+y≡x+𝕤y] : (𝕤 x) + y ≡ x + (𝕤 y)
   [𝕤x+y≡x+𝕤y] = ≡-⇶ [𝕤x+y≡𝕤[x+y]] [𝕤[x+y]≡x+𝕤y]

   [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] : (𝕤 ((𝕤 x) + y)) ≡ (𝕤 ( x + (𝕤 y)))
   [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((𝕤 x) + y) ( x + (𝕤 y)) [𝕤x+y≡x+𝕤y]

-- b)
   [𝕤[x+𝕤y]≡𝕤x+𝕤y] : (𝕤 (x + (𝕤 y))) ≡ (𝕤 x) + (𝕤 y)
   [𝕤[x+𝕤y]≡𝕤x+𝕤y] = 𝕤[x+y]≡𝕤x+y x (𝕤 y)   

-- Goal:   
   [𝕤[𝕤x+y]≡𝕤x+𝕤y] :  (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
   [𝕤[𝕤x+y]≡𝕤x+𝕤y] = ≡-⇶ [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] 
                                   [𝕤[x+𝕤y]≡𝕤x+𝕤y]

{-
       [𝕤[𝕤x+y]≡𝕤x+𝕤y]
    ___________|_________________
   |                             |
            a)           b)
   [𝕤[𝕤x+y] ≡  𝕤[x+𝕤y]  ≡  𝕤x+𝕤y]
           ^             ^
          𝕤|             |
      [𝕤x+y≡x+𝕤y]        |
           ^             |
           |       𝕤[x+y]≡𝕤x+y
         ≡-⇶            /\               
           |            x  𝕤y
  [𝕤x+y≡𝕤[x+y] ≡ x+𝕤y]
       ^        ^
       |        |
   𝕤x+y≡𝕤[x+y]  |
       /\       |
      x  y      |
           [𝕤[x+y]≡x+𝕤y] -- ind. hyp.
  
-}

-- final step for 𝕤[x+y]≡x+𝕤y
𝕤[x+y]≡x+𝕤y : (x y : ℕ) → 𝕤 (x + y) ≡ x + (𝕤 y)
𝕤[x+y]≡x+𝕤y 𝕫 y  = 𝕤[𝕫+y]≡𝕫+𝕤y y
𝕤[x+y]≡x+𝕤y (𝕤 x) y = [𝕤[𝕤x+y]≡𝕤x+𝕤y]
 where
  [𝕤[𝕤x+y]≡𝕤x+𝕤y] : (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
  [𝕤[𝕤x+y]≡𝕤x+𝕤y] = [𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y] x y (𝕤[x+y]≡x+𝕤y x y)

x+𝕤y≡𝕤[x+y] : (x y : ℕ) → x + (𝕤 y) ≡ (𝕤 (x + y))
x+𝕤y≡𝕤[x+y] x y = ≡-↑↓ (𝕤[x+y]≡x+𝕤y x y)








-- 11) [a+x]+y≡x+[a+y]

-- Base case for [a+x]+y≡x+[a+y]
[𝕫+x]+y≡x+[𝕫+y] : (x y : ℕ) → (𝕫 + x) + y ≡ x + (𝕫 + y)
[𝕫+x]+y≡x+[𝕫+y] x y = ⟲ (x + y)


-- Inductive step for [a+x]+y≡x+[a+y]

[[a+x]+y≡x+[a+y]]→[[𝕤a+x]+y≡x+[𝕤a+y]] : (x y a : ℕ) → (a + x) + y ≡ x + (a + y) → ((𝕤 a) + x) + y ≡ x + ((𝕤 a) + y)
[[a+x]+y≡x+[a+y]]→[[𝕤a+x]+y≡x+[𝕤a+y]] x y a [[a+x]+y≡x+[a+y]] = [[𝕤a+x]+y≡x+[𝕤a+y]]
 where

-- Defs
  +y : ℕ → ℕ
  +y = _+'_ y

  x+ : ℕ → ℕ
  x+ = _+_ x


--  a)
  [𝕤a+x≡𝕤[a+x]] : (𝕤 a) + x ≡ (𝕤 (a + x))
  [𝕤a+x≡𝕤[a+x]] = 𝕤x+y≡𝕤[x+y] a x

  [[𝕤a+x]+y≡𝕤[a+x]+y] : ((𝕤 a) + x) + y ≡ (𝕤 (a + x)) + y
  [[𝕤a+x]+y≡𝕤[a+x]+y] = [f≡g]→[fa≡ga]₂ +y +y (⟲ +y) ((𝕤 a) + x) (𝕤 (a + x)) [𝕤a+x≡𝕤[a+x]]


--  b)
  [𝕤[a+x]+y≡𝕤[[a+x]+y]] : (𝕤 (a + x)) + y ≡ (𝕤 ((a + x) + y))
  [𝕤[a+x]+y≡𝕤[[a+x]+y]] = 𝕤x+y≡𝕤[x+y] (a + x) y



--  c)  
  [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] : (𝕤 ((a + x) + y)) ≡ (𝕤 (x + (a + y)))
  [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((a + x) + y) (x + (a + y)) [[a+x]+y≡x+[a+y]]


--  d)
  [𝕤[x+[a+y]]≡x+𝕤[a+y]] : (𝕤 (x + (a + y))) ≡ x + (𝕤 (a + y))
  [𝕤[x+[a+y]]≡x+𝕤[a+y]] = 𝕤[x+y]≡x+𝕤y x (a + y)

  
--  e)
  
  [𝕤[a+y]≡𝕤a+y] : (𝕤 (a + y)) ≡ (𝕤 a) + y
  [𝕤[a+y]≡𝕤a+y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] a y)
  
  [x+𝕤[a+y]≡x+[𝕤a+y]] : x + (𝕤 (a + y)) ≡ x + ((𝕤 a) + y)
  [x+𝕤[a+y]≡x+[𝕤a+y]] = [f≡g]→[fa≡ga]₂ (x+) (x+) (⟲ x+) (𝕤 (a + y)) ((𝕤 a) + y) [𝕤[a+y]≡𝕤a+y]
 

-- Goal:
  [[𝕤a+x]+y≡x+[𝕤a+y]] : ((𝕤 a) + x) + y ≡ x + ((𝕤 a) + y)
  [[𝕤a+x]+y≡x+[𝕤a+y]] = 
    ≡-⇶ [[𝕤a+x]+y≡𝕤[a+x]+y] (             --a
             ≡-⇶ [𝕤[a+x]+y≡𝕤[[a+x]+y]] (           --b
                      ≡-⇶ [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] (         --c
                                 ≡-⇶ [𝕤[x+[a+y]]≡x+𝕤[a+y]]             --d
                                                 [x+𝕤[a+y]≡x+[𝕤a+y]]                --e
                       )))

  

-- Diagram :
{-
                           [[𝕤a+x]+y ≡ x+[𝕤a+y]]
                                     ^
  ___________________________________|_____________________________________________
  |                                                                                |
            a)         b)            c)                   d)            e)
  [[𝕤a+x]+y ≡ 𝕤[a+x]+y ≡ 𝕤[[a+x]+y] ≡ 𝕤[x+[a+y]]          ≡   x+𝕤[a+y] ≡ x+[𝕤a+y]]     
           ^            ^           ^                      ^             ^  
           |+y          |          𝕤|                      |             |
           |            |  [[a+x]+y]≡x+[a+y]] -- ind-hyp   |             | x+
      [𝕤a+x≡𝕤[a+x]]     |                                  |             |
           ^      𝕤[x+y]≡𝕤x+y                              |      [𝕤[a+y]≡𝕤a+y]
           |           / \                           𝕤[x+y]≡x+𝕤y         ^
           |         a+x  y                               /\             |
           |                                             x  a+y    𝕤[x+y]≡𝕤x+y
       𝕤x+y≡𝕤[x+y]                                                      /\
          / \                                                          a  y
         a   x
-}


-- final step for [a+x]+y≡x+[a+y]
[a+x]+y≡x+[a+y] : (x y a : ℕ) → (a + x) + y ≡ x + (a + y)
[a+x]+y≡x+[a+y] x y 𝕫 = [𝕫+x]+y≡x+[𝕫+y] x y
[a+x]+y≡x+[a+y] x y (𝕤 n) = [[a+x]+y≡x+[a+y]]→[[𝕤a+x]+y≡x+[𝕤a+y]] x y n ([a+x]+y≡x+[a+y] x y n)

x+[a+y]≡[a+x]+y : (x y a : ℕ) → x + (a + y) ≡ (a + x) + y
x+[a+y]≡[a+x]+y x y a = ≡-↑↓ ([a+x]+y≡x+[a+y] x y a)






-- 12) addition is commutative
x+y≡y+x : (x y : ℕ) → x + y ≡ y + x
x+y≡y+x x y = [x+y≡y+x]
 where

-- Defs :
  x+ : ℕ → ℕ
  x+ = _+_ x

-- a)
  [y≡y+𝕫] : y ≡ y + 𝕫
  [y≡y+𝕫] = x≡x+𝕫 y

  [x+y≡x+[y+𝕫]] : x + y ≡ x + (y + 𝕫)
  [x+y≡x+[y+𝕫]] = [f≡g]→[fa≡ga]₂ x+ x+ (⟲ x+) y (y + 𝕫) [y≡y+𝕫]

-- b)
  [x+[y+𝕫]≡[y+x]+𝕫] : x + (y + 𝕫) ≡ (y + x) + 𝕫
  [x+[y+𝕫]≡[y+x]+𝕫] = x+[a+y]≡[a+x]+y x 𝕫 y

-- c)

  [[y+x]+𝕫≡y+x] : (y + x) + 𝕫 ≡ y + x
  [[y+x]+𝕫≡y+x] = x+𝕫≡x (y + x)
 
-- Goal: 

  [x+y≡y+x] : x + y ≡ y + x
  [x+y≡y+x] = ≡-⇶ [x+y≡x+[y+𝕫]] (
                  ≡-⇶ [x+[y+𝕫]≡[y+x]+𝕫]
                               [[y+x]+𝕫≡y+x]
              )

{-
               [x+y≡y+x]
                   ^
    _______________|_______________
    |                              |
         a)        b)         c)
    [x+y ≡ x+[y+𝕫] ≡ [y+x]+𝕫 ≡ y+x]
         ^          ^         ^  
         |          |         |
       x+|   x+[a+y]≡[a+x]+y  |
         |         /|\        |
       [y≡y+𝕫]    x 𝕫 y       |
         ^                 x+𝕫≡x
         |                    |  
        x=x+𝕫                y+x
         |
         y
  
-}






-- 13) addition is associative
[a+b]+c≡a+[b+c] : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
[a+b]+c≡a+[b+c] a b c = [[a+b]+c≡a+[b+c]]
 where

-- Defs :
  +c : ℕ → ℕ
  +c = _+'_ c

-- a)

  [a+b≡b+a] : a + b ≡ b + a
  [a+b≡b+a] = x+y≡y+x a b

  [[a+b]+c≡[b+a]+c] : (a + b) + c ≡ (b + a) + c
  [[a+b]+c≡[b+a]+c] = [f≡g]→[fa≡ga]₂ +c +c (⟲ +c) (a + b) (b + a) [a+b≡b+a]  

-- b)
  [[b+a]+c≡a+[b+c]] : (b + a) + c ≡ a + (b + c)
  [[b+a]+c≡a+[b+c]] = [a+x]+y≡x+[a+y] a c b
  
-- Goal:
  [[a+b]+c≡a+[b+c]] : (a + b) + c ≡ a + (b + c)
  [[a+b]+c≡a+[b+c]] = ≡-⇶ [[a+b]+c≡[b+a]+c] [[b+a]+c≡a+[b+c]]

{-
                [[a+b]+c≡a+[b+c]]
       _________________|___________________
       |                                    |
                  a)            b)
       [[a+b]+c   ≡   [b+a]+c   ≡   a+[b+c]]
                ^               ^  
              +c|               |
            [a+b≡b+a]           |
                ^        [a+x]+y≡x+[a+y]
                |              /|\
             x+y≡y+x          a c b
                /\
               a  b
 

-}



-- 14) 0 is a unique right identity for ℕ 

-- base case
[0+y≡0]→[y≡0] : (y : ℕ) → 0 + y ≡ 0 → y ≡ 0
[0+y≡0]→[y≡0] y [0+y≡0] = [y≡0]
 where
  [y≡0+y] : y ≡ 0 + y
  [y≡0+y] = x≡𝕫+x y

  [y≡0] : y ≡ 0
  [y≡0] = ≡-⇶ [y≡0+y] [0+y≡0]
  
-- inductive step
[[x+y≡x]→[y≡0]]→[[𝕤x+y≡𝕤x]→[y≡0]] : (x y : ℕ) → ((x + y ≡ x) → (y ≡ 0)) → ((𝕤 x) + y ≡ (𝕤 x)) → y ≡ 0
[[x+y≡x]→[y≡0]]→[[𝕤x+y≡𝕤x]→[y≡0]] x y [[x+y≡x]→[y≡0]] [𝕤x+y≡𝕤x] = [y≡0]
 where
  [𝕤[x+y]≡𝕤x+y] : (𝕤 (x + y)) ≡  (𝕤 x) + y
  [𝕤[x+y]≡𝕤x+y] = 𝕤[x+y]≡𝕤x+y x y

  [𝕤[x+y]≡𝕤x] : (𝕤 (x + y)) ≡ (𝕤 x)
  [𝕤[x+y]≡𝕤x] = ≡-⇶ [𝕤[x+y]≡𝕤x+y] [𝕤x+y≡𝕤x]

  [x+y≡x] : x + y ≡ x
  [x+y≡x] = [𝕤x≡𝕤y]→[x≡y] (x + y) x [𝕤[x+y]≡𝕤x]

  [y≡0] : y ≡ 0
  [y≡0] = [[x+y≡x]→[y≡0]] [x+y≡x]

-- final step
[x+y≡x]→[y≡0] : (x y : ℕ) → x + y ≡ x → y ≡ 0
[x+y≡x]→[y≡0] 0 y = [0+y≡0]→[y≡0] y 
[x+y≡x]→[y≡0] (𝕤 x) y = [[x+y≡x]→[y≡0]]→[[𝕤x+y≡𝕤x]→[y≡0]] x y ([x+y≡x]→[y≡0] x y)



-- 15) 0 is a unique left identity for ℕ


[y+x≡x]→[y≡0] : (x y : ℕ) → y + x ≡ x → y ≡ 0
[y+x≡x]→[y≡0] x y [y+x≡x] = [y≡0]
 where
  [x+y≡y+x] : x + y ≡ y + x
  [x+y≡y+x] = x+y≡y+x x y

  [x+y≡x] : x + y ≡ x
  [x+y≡x] = ≡-⇶ [x+y≡y+x] [y+x≡x]

  [y≡0] : y ≡ 0
  [y≡0] = [x+y≡x]→[y≡0] x y [x+y≡x]



-- 16) If x + y ≡ 0, then x ≡ 0 and y ≡ 0
[x+0≡0]→[[x≡0]∧[0≡0]] : (x : ℕ) → x + 0 ≡ 0 → x ≡ 0 ∧ 0 ≡ 0
[x+0≡0]→[[x≡0]∧[0≡0]] x [x+0≡0] = ∧-cons [x≡0] (⟲ 0)
 where
  [x≡0] : x ≡ 0
  [x≡0] = [y+x≡x]→[y≡0] 0 x [x+0≡0]

[[x+y≡0]→[[x≡0]∧[y≡0]]]→[[x+𝕤y≡0]→[[x≡0]∧[𝕤y≡0]]] : (x y : ℕ) → (x + y ≡ 0 → x ≡ 0 ∧ y ≡ 0) → x + (𝕤 y) ≡ 0 → x ≡ 0 ∧ (𝕤 y) ≡ 0
[[x+y≡0]→[[x≡0]∧[y≡0]]]→[[x+𝕤y≡0]→[[x≡0]∧[𝕤y≡0]]] x y [[x+y≡0]→[[x≡0]∧[y≡0]]] [x+𝕤y≡0] = ∧-cons [x≡0] [𝕤y≡0]
 where
  [𝕤[x+y]≡x+𝕤y] : (𝕤 (x + y)) ≡ x + (𝕤 y)
  [𝕤[x+y]≡x+𝕤y] = 𝕤[x+y]≡x+𝕤y x y
  
  [𝕤[x+y]≡0] : (𝕤 (x + y)) ≡ 0
  [𝕤[x+y]≡0] = ≡-⇶ [𝕤[x+y]≡x+𝕤y] [x+𝕤y≡0]
  
  ☢ : ⊥
  ☢ = 𝕤x≠𝕫 (x + y) [𝕤[x+y]≡0]

  [x≡0] : x ≡ 0
  [x≡0] = ω ☢

  [𝕤y≡0] : (𝕤 y) ≡ 0
  [𝕤y≡0] = ω ☢


[x+y≡0]→[[x≡0]∧[y≡0]] : (x y : ℕ) → x + y ≡ 0 → x ≡ 0 ∧ y ≡ 0
[x+y≡0]→[[x≡0]∧[y≡0]] x 𝕫 = [x+0≡0]→[[x≡0]∧[0≡0]] x
[x+y≡0]→[[x≡0]∧[y≡0]] x (𝕤 y) = [[x+y≡0]→[[x≡0]∧[y≡0]]]→[[x+𝕤y≡0]→[[x≡0]∧[𝕤y≡0]]] x y ([x+y≡0]→[[x≡0]∧[y≡0]] x y)






-- SECTION : ordering; >, <, ≥, ≤ 

-- 1)  (x < y) → (x ≤ y)
-- 2)  (x > y) → (x ≥ y)
-- 3)  (x ≰ y) → (x ≮ y)
-- 4)  (x ≱ y) → (x ≯ y)
-- 5)  (x < y) → (x ≱ y)
-- 6)  (x > y) → (x ≰ y)
-- 7)  Every x ∈ ℕ is greater than or equal to 0
-- 8)  1 > 0
-- 9)  x+1 > x
-- 10) x < x+1
-- 11) The successor of any natural number is greater than 0
-- 12) Every natural number is greater than or equal to itself
-- 13) ≤ is transitive
-- 14) < is transitive
-- 15) If x ≥ y, then 𝕤x > y
-- 16) If x ≤ y, then x < 𝕤y
-- 17) No natural number is greater than itself

-- 1) less than implies less than or equal
[x<y]→[x≤y] : (x y : ℕ) → x < y → x ≤ y
[x<y]→[x≤y] x y (a , (b , (∧-cons [𝕤b≡a] [x+a≡y]))) = (a , [x+a≡y])

-- 2) greater than implies greater than or equal
[x>y]→[x≥y] : (x y : ℕ) → x > y → x ≥ y
[x>y]→[x≥y] x y (a , (b , (∧-cons [𝕤b≡a] [y+a≡x]))) = (a , [y+a≡x])

-- 3) x ≰ y  →  x ≮ y
[x≰y]→[x≮y] : (x y : ℕ) → x ≰ y → x ≮ y
[x≰y]→[x≮y] x y [x≰y] [x<y] = ☢
 where
  [x≤y] : x ≤ y
  [x≤y] = [x<y]→[x≤y] x y [x<y]

  ☢ : ⊥
  ☢ = [x≰y] [x≤y]

-- 4) x ≱ y  →  x ≯ y
[x≱y]→[x≯y] : (x y : ℕ) → x ≱ y → x ≯ y
[x≱y]→[x≯y] x y [x≱y] [x>y] = ☢
 where
  [x≥y] : x ≥ y
  [x≥y] = [x>y]→[x≥y] x y [x>y]

  ☢ : ⊥
  ☢ = [x≱y] [x≥y]


-- 5) x < y  → x ≱ y
[x<y]→[x≱y] : (x y : ℕ) → x < y → x ≱ y
[x<y]→[x≱y] x y (a , (a' , (∧-cons [𝕤a'≡a] [x+a≡y]))) (b , [y+b≡x]) = ☢
 where
  +a : ℕ → ℕ
  +a = _+'_ a

  [[y+b]+a≡x+a] : (y + b) + a ≡ x + a
  [[y+b]+a≡x+a] = [f≡g]→[fa≡ga]₂ +a +a (⟲ +a) (y + b) x [y+b≡x]

  [[y+b]+a≡y] : (y + b) + a ≡ y
  [[y+b]+a≡y] = ≡-⇶ [[y+b]+a≡x+a] [x+a≡y]

  [y+[b+a]≡[y+b]+a] : y + (b + a) ≡ (y + b) + a
  [y+[b+a]≡[y+b]+a] = ≡-↑↓ ([a+b]+c≡a+[b+c] y b a)

  [y+[b+a]≡y] : y + (b + a) ≡ y
  [y+[b+a]≡y] = ≡-⇶ [y+[b+a]≡[y+b]+a] [[y+b]+a≡y]

  [b+a≡0] : b + a ≡ 0
  [b+a≡0] = [x+y≡x]→[y≡0] y (b + a) [y+[b+a]≡y]

  [b≡0∧a≡0] : b ≡ 0 ∧ a ≡ 0
  [b≡0∧a≡0] = [x+y≡0]→[[x≡0]∧[y≡0]] b a [b+a≡0]

  [a≡0] : a ≡ 0
  [a≡0] = ∧-π₂ [b≡0∧a≡0]
 
  [𝕤a'≡0] : (𝕤 a') ≡ 0
  [𝕤a'≡0] = ≡-⇶ [𝕤a'≡a] [a≡0]

  ☢ : ⊥
  ☢ = 𝕤x≠𝕫 a' [𝕤a'≡0]


-- 6) x > y  → x ≰ y
[x>y]→[x≰y] : (x y : ℕ) → x > y → x ≰ y
[x>y]→[x≰y] x y (a , (a' , (∧-cons [𝕤a'≡a] [y+a≡x]))) (b , [x+b≡y]) = ☢
 where
-- Defs :
  +b : ℕ → ℕ
  +b = _+'_ b

  [[y+a]+b≡x+b] : (y + a) + b ≡ x + b
  [[y+a]+b≡x+b] = [f≡g]→[fa≡ga]₂ +b +b (⟲ +b) (y + a) x [y+a≡x]

  [[y+a]+b≡y] : (y + a) + b ≡ y
  [[y+a]+b≡y] = ≡-⇶ [[y+a]+b≡x+b] [x+b≡y]

  [y+[a+b]≡[y+a]+b] : y + (a + b) ≡ (y + a) + b
  [y+[a+b]≡[y+a]+b] = ≡-↑↓ ([a+b]+c≡a+[b+c] y a b)

  [y+[a+b]≡y] : y + (a + b) ≡ y
  [y+[a+b]≡y] = ≡-⇶ [y+[a+b]≡[y+a]+b] [[y+a]+b≡y]

  [a+b≡0] : a + b ≡ 0
  [a+b≡0] = [x+y≡x]→[y≡0] y (a + b) [y+[a+b]≡y]

  [a≡0∧b≡0] : a ≡ 0 ∧ b ≡ 0
  [a≡0∧b≡0] = [x+y≡0]→[[x≡0]∧[y≡0]] a b [a+b≡0] 
 
  [a≡0] : a ≡ 0
  [a≡0] = ∧-π₁ [a≡0∧b≡0]

  [𝕤a'≡0] : (𝕤 a') ≡ 0
  [𝕤a'≡0] = ≡-⇶ [𝕤a'≡a] [a≡0]

  ☢ : ⊥
  ☢ = 𝕤x≠𝕫 a' [𝕤a'≡0]


-- 7) Every x ∈ ℕ is greater than or equal to 0
x≥𝕫 : (x : ℕ) → x ≥ 𝕫
x≥𝕫 x = (x , 𝕫+x≡x x)

-- 8) 1 > 0
𝕤𝕫>𝕫 : 𝕤 𝕫 > 𝕫
𝕤𝕫>𝕫 = (𝕤 𝕫 , (𝕫 , ∧-cons (⟲ (𝕤 𝕫)) [[𝕫+𝕤𝕫]≡𝕤𝕫]))
 where
  [[𝕫+𝕤𝕫]≡𝕤𝕫] : 𝕫 + (𝕤 𝕫) ≡ (𝕤 𝕫)
  [[𝕫+𝕤𝕫]≡𝕤𝕫] = 𝕫+x≡x (𝕤 𝕫)   

-- 9) x+1 > x
𝕤x>x : (x : ℕ) → 𝕤 x > x
𝕤x>x x = (𝕤 𝕫 , (𝕫 , (∧-cons (⟲ (𝕤 𝕫)) (x+𝕤𝕫≡𝕤x x))))

-- 10) x < x+1
x<𝕤x : (x : ℕ) → x < 𝕤 x
x<𝕤x x = (𝕤 𝕫 , (𝕫 , (∧-cons (⟲ (𝕤 𝕫)) (x+𝕤𝕫≡𝕤x x))))


-- 11) The successor of any x ∈ ℕ is greater than 0
-- inductive step
[𝕤x>𝕫]→[𝕤𝕤x>𝕫] : (x : ℕ) → (𝕤 x) > 𝕫 → (𝕤 (𝕤 x)) > 𝕫
[𝕤x>𝕫]→[𝕤𝕤x>𝕫] x (a , (b , (∧-cons [𝕤b≡a] [𝕫+a≡𝕤x]))) = ((𝕤 a) , ((𝕤 b) , (∧-cons [𝕤𝕤b≡𝕤a] [𝕫+𝕤a≡𝕤𝕤x])))
 where
  [𝕤𝕤b≡𝕤a] : (𝕤 (𝕤 b)) ≡ (𝕤 a)
  [𝕤𝕤b≡𝕤a] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (𝕤 b) a [𝕤b≡a]

  [𝕤[𝕫+a]≡𝕤𝕤x] : (𝕤 (𝕫 + a)) ≡ (𝕤 (𝕤 x))
  [𝕤[𝕫+a]≡𝕤𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (𝕫 + a) (𝕤 x) [𝕫+a≡𝕤x]

  [𝕤[𝕫+a]≡𝕫+𝕤a] : (𝕤 (𝕫 + a)) ≡ 𝕫 + (𝕤 a)
  [𝕤[𝕫+a]≡𝕫+𝕤a] = 𝕤[x+y]≡x+𝕤y 𝕫 a

  [𝕫+𝕤a≡𝕤𝕤x] : 𝕫 + (𝕤 a) ≡ (𝕤 (𝕤 x))
  [𝕫+𝕤a≡𝕤𝕤x] = ≡-⇶ (≡-↑↓ [𝕤[𝕫+a]≡𝕫+𝕤a]) [𝕤[𝕫+a]≡𝕤𝕤x]

-- final step
𝕤x>𝕫 : (x : ℕ) → (𝕤 x) > 𝕫
𝕤x>𝕫 𝕫 = 𝕤𝕫>𝕫
𝕤x>𝕫 (𝕤 n) = [𝕤x>𝕫]→[𝕤𝕤x>𝕫] n (𝕤x>𝕫 n)


-- 12) Every x ∈ ℕ is greater than or equal to itself
x≥x : (x : ℕ) → x ≥ x
x≥x x = (𝕫 , (x+𝕫≡x x))

-- 13) ≤ is transitive
x≤y→y≤z→x≤z : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
x≤y→y≤z→x≤z x y z (a , [x+a≡y]) (b , [y+b≡z]) = ((a + b) , [x+[a+b]≡z])
 where
--  [x+a≡y]
--  [y+b≡z]
  
-- Defs:
  +b : ℕ → ℕ
  +b = _+'_ b

  [[x+a]+b≡y+b] : (x + a) + b ≡ y + b
  [[x+a]+b≡y+b] = [f≡g]→[fa≡ga]₂ +b +b (⟲ +b) (x + a) y [x+a≡y]
 
  [[x+a]+b≡x+[a+b]] : (x + a) + b ≡ x + (a + b)
  [[x+a]+b≡x+[a+b]] = [a+b]+c≡a+[b+c] x a b

  [x+[a+b]≡y+b] : x + (a + b) ≡ y + b
  [x+[a+b]≡y+b] = ≡-⇶ (≡-↑↓ [[x+a]+b≡x+[a+b]]) [[x+a]+b≡y+b]
 

  [x+[a+b]≡z] : x + (a + b) ≡ z
  [x+[a+b]≡z] = ≡-⇶ [x+[a+b]≡y+b] [y+b≡z]

-- 14) < is transitive
x<y→y<z→x<z : (x y z : ℕ) → x < y → y < z → x < z
x<y→y<z→x<z 
 x y z 
 (a , (a' , (∧-cons [𝕤a'≡a] [x+a≡y]))) 
 (b , (b' ,(∧-cons [𝕤b'≡b] [y+b≡z]))) 

 = ((a + b) , ( (𝕤 (a' + b')) , (∧-cons [𝕤𝕤[a'+b']≡a+b] [x+[a+b]≡z])))
   
 where
-- [𝕤a'≡a]
-- [𝕤b'≡b]
   
-- Defs :
   +b : ℕ → ℕ
   +b = _+'_ b

   a'+ : ℕ → ℕ
   a'+ = _+_ a'

   [𝕤a'+b≡a+b] : (𝕤 a') + b ≡ a + b
   [𝕤a'+b≡a+b] = [f≡g]→[fa≡ga]₂ +b +b (⟲ +b) (𝕤 a') a [𝕤a'≡a]
 
   [𝕤a'+b≡𝕤[a'+b]] : (𝕤 a') + b ≡ 𝕤 (a' + b)
   [𝕤a'+b≡𝕤[a'+b]] = 𝕤x+y≡𝕤[x+y] a' b

   [a'+b≡a'+𝕤b'] : a' + b ≡ a' + (𝕤 b')
   [a'+b≡a'+𝕤b'] = [f≡g]→[fa≡ga]₂ a'+ a'+ (⟲ a'+) b (𝕤 b') (≡-↑↓ [𝕤b'≡b])

   [𝕤[a'+b']≡a'+𝕤b'] : (𝕤 (a' + b')) ≡ a' + (𝕤 b')
   [𝕤[a'+b']≡a'+𝕤b'] = 𝕤[x+y]≡x+𝕤y a' b'

   [𝕤[a'+b]≡𝕤[a'+𝕤b']] : (𝕤 (a' + b)) ≡ (𝕤 (a' + (𝕤 b')))
   [𝕤[a'+b]≡𝕤[a'+𝕤b']] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (a' + b) (a' + (𝕤 b')) [a'+b≡a'+𝕤b']

   [𝕤[a'+𝕤b']≡𝕤𝕤[a'+b']] : (𝕤 (a' + (𝕤 b'))) ≡ (𝕤 (𝕤 (a' + b')))
   [𝕤[a'+𝕤b']≡𝕤𝕤[a'+b']] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (a' + (𝕤 b')) (𝕤 (a' + b')) (≡-↑↓ [𝕤[a'+b']≡a'+𝕤b'])

   [𝕤[a'+b]≡𝕤𝕤[a'+b']] : (𝕤 (a' + b)) ≡ (𝕤 (𝕤 (a' + b')))
   [𝕤[a'+b]≡𝕤𝕤[a'+b']] = ≡-⇶ [𝕤[a'+b]≡𝕤[a'+𝕤b']] [𝕤[a'+𝕤b']≡𝕤𝕤[a'+b']]

   [𝕤a'+b≡𝕤𝕤[a'+b']] : (𝕤 a') + b ≡ (𝕤 (𝕤 (a' + b')))
   [𝕤a'+b≡𝕤𝕤[a'+b']] = ≡-⇶ [𝕤a'+b≡𝕤[a'+b]] [𝕤[a'+b]≡𝕤𝕤[a'+b']]
    
   [𝕤𝕤[a'+b']≡a+b] : (𝕤 (𝕤 (a' + b'))) ≡ a + b
   [𝕤𝕤[a'+b']≡a+b] = ≡-↑↓ (≡-⇶ (≡-↑↓ [𝕤a'+b≡a+b]) [𝕤a'+b≡𝕤𝕤[a'+b']])

   [[x+a]+b≡y+b] : (x + a) + b ≡ y + b
   [[x+a]+b≡y+b] = [f≡g]→[fa≡ga]₂ +b +b (⟲ +b) (x + a) y [x+a≡y]

   [[x+a]+b≡z] : (x + a) + b ≡ z
   [[x+a]+b≡z] = ≡-⇶ [[x+a]+b≡y+b] [y+b≡z]

   [[x+a]+b≡x+[a+b]] : (x + a) + b ≡ x + (a + b)
   [[x+a]+b≡x+[a+b]] = [a+b]+c≡a+[b+c] x a b
  
   [x+[a+b]≡z] : x + (a + b) ≡ z
   [x+[a+b]≡z] = ≡-⇶ (≡-↑↓ [[x+a]+b≡x+[a+b]]) [[x+a]+b≡z]


-- 15) If x is greater than or equal to y, then 𝕤x is greater than y
[x≥y]→[𝕤x>y] : (x y : ℕ) → x ≥ y → (𝕤 x) > y
[x≥y]→[𝕤x>y] x y (a , [y+a≡x]) = (b , (b' , (∧-cons [𝕤b'≡b] [y+b≡𝕤x])))
 where
  b : ℕ
  b = 𝕤 a

  b' : ℕ
  b' = a

  [𝕤b'≡b] : (𝕤 b') ≡ b
  [𝕤b'≡b] = ⟲ (𝕤 a)

  [𝕤[y+b']≡𝕤x] : (𝕤 (y + b')) ≡ (𝕤 x)
  [𝕤[y+b']≡𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (y + b') x [y+a≡x]

  [y+b≡𝕤[y+b']] : y + b ≡ (𝕤 (y + b'))
  [y+b≡𝕤[y+b']] = x+𝕤y≡𝕤[x+y] y b'

  [y+b≡𝕤x] : y + b ≡ (𝕤 x)
  [y+b≡𝕤x] = ≡-⇶ [y+b≡𝕤[y+b']] [𝕤[y+b']≡𝕤x]


-- 16) If x is less than or equal to y, then x is less than 𝕤y
[x≤y]→[x<𝕤y] : (x y : ℕ) → x ≤ y → x < (𝕤 y)
[x≤y]→[x<𝕤y] x y (a , [x+a≡y]) = (b , (b' , (∧-cons [𝕤b'≡b] [x+b≡𝕤y])))
 where
  b : ℕ
  b = 𝕤 a
  
  b' : ℕ
  b' = a

  [𝕤b'≡b] : (𝕤 b') ≡ b
  [𝕤b'≡b] = ⟲ (𝕤 a)

  [𝕤[x+b']≡𝕤y] : (𝕤 (x + b')) ≡ (𝕤 y)
  [𝕤[x+b']≡𝕤y] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (x + b') y [x+a≡y]

  [x+b≡𝕤[x+b']] : x + b ≡ (𝕤 (x + b'))
  [x+b≡𝕤[x+b']] = x+𝕤y≡𝕤[x+y] x b'
  
  [x+b≡𝕤y] : x + b ≡ (𝕤 y)
  [x+b≡𝕤y] = ≡-⇶ [x+b≡𝕤[x+b']] [𝕤[x+b']≡𝕤y]


-- 17) No natural number is greater than itself
x≯x : (x : ℕ) → x ≯ x
x≯x x (a , (b , (∧-cons [𝕤b≡a] [x+a≡x]))) = ☢
 where
  [a≡0] : a ≡ 0
  [a≡0] = [x+y≡x]→[y≡0] x a [x+a≡x]

  [𝕤b≡0] : (𝕤 b) ≡ 0
  [𝕤b≡0] = ≡-⇶ [𝕤b≡a] [a≡0]
  
  ☢ : ⊥
  ☢ = 𝕤x≠𝕫 b [𝕤b≡0]












-- even and odd

-- 1) 𝕫 is even
-- 2) 𝕫 is not odd
-- 3) 𝕤𝕫 is not even
-- 4) 𝕤𝕫 is odd
-- 5) if n is even then 𝕤𝕤n is even
-- 6) if x is even then 𝕤x is not

-- 1) 𝕫 is even
even-𝕫≡𝕥 : even 𝕫 ≡ 𝕥
even-𝕫≡𝕥 = ⟲ 𝕥

-- 2) 𝕫 is not odd
odd-𝕫≡𝕗 : odd 𝕫 ≡ 𝕗
odd-𝕫≡𝕗 = ⟲ 𝕗

-- 3) 𝕤𝕫 is not even
even-𝕤𝕫≡𝕗 : (even (𝕤 𝕫)) ≡ 𝕗
even-𝕤𝕫≡𝕗 = ⟲ 𝕗

-- 4) 𝕤𝕫 is odd
odd-𝕤𝕫≡𝕥 : (odd (𝕤 𝕫)) ≡ 𝕥
odd-𝕤𝕫≡𝕥 = ⟲ 𝕥


[even-𝕫≡𝕥]→[even-𝕤𝕫≡𝕗] : (even 𝕫) ≡ 𝕥 → (even (𝕤 𝕫)) ≡ 𝕗
[even-𝕫≡𝕥]→[even-𝕤𝕫≡𝕗] [even-𝕫≡𝕥] = ⟲ 𝕗

-- 5) if n is even then 𝕤𝕤n is even
-- base case
even-𝕫≡even-𝕤𝕤𝕫 : (even 𝕫) ≡ even (𝕤 (𝕤 𝕫))
even-𝕫≡even-𝕤𝕤𝕫 = ⟲ 𝕥

-- inductive step
[even-n≡even-𝕤𝕤n]→[even-𝕤n≡even-𝕤𝕤𝕤n] : (n : ℕ) → (even n) ≡ (even (𝕤 (𝕤 n))) → (even (𝕤 n)) ≡ (even (𝕤 (𝕤 (𝕤 n))))
[even-n≡even-𝕤𝕤n]→[even-𝕤n≡even-𝕤𝕤𝕤n] n [even-n≡even-𝕤𝕤n] = ⟲ (even (𝕤 n))

-- final step
even-n≡even-𝕤𝕤n : (n : ℕ) → (even n) ≡ (even (𝕤 (𝕤 n)))
even-n≡even-𝕤𝕤n 𝕫 = even-𝕫≡even-𝕤𝕤𝕫
even-n≡even-𝕤𝕤n (𝕤 n) = [even-n≡even-𝕤𝕤n]→[even-𝕤n≡even-𝕤𝕤𝕤n] n (even-n≡even-𝕤𝕤n n)


-- 6) If x is even then 𝕤x is even 
-- base case
[even-𝕫≠even-𝕤𝕫] : (even 𝕫) ≠ (even (𝕤 𝕫))
[even-𝕫≠even-𝕤𝕫] [even-𝕫≡even-𝕤𝕫] = ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [even-𝕫≡even-𝕤𝕫]

-- inductive step
[even-x≠even-𝕤x]→[even-𝕤x≠even-𝕤𝕤x] : (x : ℕ) → (even x) ≠ (even (𝕤 x)) → (even (𝕤 x)) ≠ (even (𝕤 (𝕤 x)))
[even-x≠even-𝕤x]→[even-𝕤x≠even-𝕤𝕤x] x [even-x≠even-𝕤x] [even-𝕤x≡even-𝕤𝕤x] = ☢
 where
  [even-𝕤𝕤x≡even-x] : (even (𝕤 (𝕤 x))) ≡ (even x) 
  [even-𝕤𝕤x≡even-x] = ≡-↑↓ (even-n≡even-𝕤𝕤n x)
  
  [even-𝕤x≡even-x] : (even (𝕤 x)) ≡ (even x)
  [even-𝕤x≡even-x] = ≡-⇶ [even-𝕤x≡even-𝕤𝕤x] [even-𝕤𝕤x≡even-x]

  ☢ : ⊥
  ☢ = [even-x≠even-𝕤x] (≡-↑↓ [even-𝕤x≡even-x])
 
-- final step
[even-x≠even-𝕤x] : (x : ℕ) → (even x) ≠ (even (𝕤 x))
[even-x≠even-𝕤x] 𝕫 = [even-𝕫≠even-𝕤𝕫]
[even-x≠even-𝕤x] (𝕤 x) = [even-x≠even-𝕤x]→[even-𝕤x≠even-𝕤𝕤x] x ([even-x≠even-𝕤x] x)







-- multiplication
-- 1) 0 * x ≡ 0
-- 2) x * 0 ≡ 0                          
-- 3) 1 * x ≡ x                          1 is a left identity for (ℕ,*)
-- 4) x * 1 ≡ x                          1 is a right identity for (ℕ,*)
-- 5) a * (b + c) ≡ a * b + a * c        Multiplication left-distributes over addition
-- 6) (a + b) * c ≡ a * c + b * c        Multiplication right-distributes over addition
-- 7) (a * x) * y ≡ x * (a * y)
-- 8) x * y ≡ y * x                      Multiplication is commutative
-- 9) (a * b) * c ≡ a * (b * c)          Multiplication is associative

-- 1) 0 * x ≡ 0
0*x≡0 : (x : ℕ) → 0 * x ≡ 0
0*x≡0 x = ⟲ 0

-- 2) x * 0 ≡ 0
--base case
0*0≡0 : 0 * 0 ≡ 0
0*0≡0 = ⟲ 0

--inductive step
[x*0≡0]→[𝕤x*0≡0] : (x : ℕ) → x * 0 ≡ 0 → (𝕤 x) * 0 ≡ 0
[x*0≡0]→[𝕤x*0≡0] x [x*0≡0] = [𝕤x*0≡0]
 where
  [𝕤x*0≡0+x*0] : (𝕤 x) * 0 ≡ 0 + x * 0
  [𝕤x*0≡0+x*0] = ⟲ (0 + x * 0)

  [0+x*0≡x*0] : 0 + x * 0 ≡ x * 0
  [0+x*0≡x*0] = 𝕫+x≡x (x * 0)

  [𝕤x*0≡0] : (𝕤 x) * 0 ≡ 0
  [𝕤x*0≡0] = ≡-⇶ [𝕤x*0≡0+x*0] (≡-⇶ [0+x*0≡x*0] [x*0≡0])

-- final step
x*0≡0 : (x : ℕ) → x * 0 ≡ 0
x*0≡0 0 = 0*0≡0
x*0≡0 (𝕤 x) = [x*0≡0]→[𝕤x*0≡0] x (x*0≡0 x)


-- 3) 1 * x ≡ x
1*x≡x : (x : ℕ) → 1 * x ≡ x
1*x≡x x = [1*x≡x] 
 where
-- Defs:
  x+ : ℕ → ℕ
  x+ = _+_ x

  [1*x≡x+[0*x]] : 1 * x ≡ x + (0 * x)
  [1*x≡x+[0*x]] = ⟲ (x + (0 * x))

  [x+[0*x]≡x+0] : x + (0 * x) ≡ x + 0
  [x+[0*x]≡x+0] = [f≡g]→[fa≡ga]₂ x+ x+ (⟲ x+) (0 * x) 0 (0*x≡0 x)

  [x+0≡x] : x + 0 ≡ x
  [x+0≡x] = x+𝕫≡x x

  [1*x≡x+0] : 1 * x ≡ x + 0
  [1*x≡x+0] = ≡-⇶ [1*x≡x+[0*x]] [x+[0*x]≡x+0]
 
  [1*x≡x] : 1 * x ≡ x
  [1*x≡x] = ≡-⇶ [1*x≡x+0] [x+0≡x]

-- 4) x * 1 ≡ x
-- base
0*1≡0 : 0 * 1 ≡ 0
0*1≡0 = ⟲ 0

-- inductive step
[x*1≡x]→[𝕤x*1≡𝕤x] : (x : ℕ) → x * 1 ≡ x → (𝕤 x) * 1 ≡ (𝕤 x)
[x*1≡x]→[𝕤x*1≡𝕤x] x [x*1≡x] = [𝕤x*1≡𝕤x]
 where
-- Defs:
  1+ : ℕ → ℕ
  1+ = _+_ 1

  [𝕤x*1≡1+x*1] : (𝕤 x) * 1 ≡ 1 + x * 1
  [𝕤x*1≡1+x*1] = ⟲ (1 + x * 1)

  [1+x*1≡1+x] : 1 + x * 1 ≡ 1 + x
  [1+x*1≡1+x] = [f≡g]→[fa≡ga]₂ 1+ 1+ (⟲ 1+) (x * 1) x [x*1≡x] 

  [1+x≡𝕤x] : 1 + x ≡ (𝕤 x)
  [1+x≡𝕤x] = 𝕤𝕫+x≡𝕤x x

  [𝕤x*1≡𝕤x] : (𝕤 x) * 1 ≡ (𝕤 x)
  [𝕤x*1≡𝕤x] = ≡-⇶ [𝕤x*1≡1+x*1] (≡-⇶ [1+x*1≡1+x] [1+x≡𝕤x])

-- final step
x*1≡x : (x : ℕ) → x * 1 ≡ x
x*1≡x 0 = 0*1≡0
x*1≡x (𝕤 x) = [x*1≡x]→[𝕤x*1≡𝕤x] x (x*1≡x x)


-- 5) Multiplication left-distributes over addition :
1-5-base<a,0> : (b c : ℕ) → 0 * (b + c) ≡ 0 * b + 0 * c
1-5-base<a,0> b c = [0*[b+c]≡0*b+0*c]
 where
  +0*c : ℕ → ℕ
  +0*c = _+'_ (0 * c)

  [0*b≡0] : 0 * b ≡ 0
  [0*b≡0] = 0*x≡0 b

  [0*c≡0] : 0 * c ≡ 0
  [0*c≡0] = 0*x≡0 c

  [0*[b+c]≡0] : 0 * (b + c) ≡ 0
  [0*[b+c]≡0] = 0*x≡0 (b + c)

  [0*b+0*c≡0+0*c] : 0 * b + 0 * c ≡ 0 + 0 * c
  [0*b+0*c≡0+0*c] = [f≡g]→[fa≡ga]₂ +0*c +0*c (⟲ +0*c) (0 * b) 0 [0*b≡0]

  [0+0*c≡0*c] : 0 + 0 * c ≡ 0 * c
  [0+0*c≡0*c] = 𝕫+x≡x (0 * c)


  [0*[b+c]≡0*b+0*c] : 0 * (b + c) ≡ 0 * b + 0 * c
  [0*[b+c]≡0*b+0*c] = ≡-⇶ [0*[b+c]≡0] (≡-↑↓ (≡-⇶ [0*b+0*c≡0+0*c] (≡-⇶ [0+0*c≡0*c] [0*c≡0])))


1-5-ind<a,𝕤> : (a b c : ℕ) → a * (b + c) ≡ a * b + a * c → (𝕤 a) * (b + c) ≡ (𝕤 a) * b + (𝕤 a) * c
1-5-ind<a,𝕤> a b c [a*[b+c]≡a*b+a*c] = [𝕤a*[b+c]≡𝕤a*b+𝕤a*c]
 where
  +𝕤a*c : ℕ → ℕ
  +𝕤a*c = _+'_ ((𝕤 a) * c)

  [b+a*b]+ : ℕ → ℕ
  [b+a*b]+ = _+_ (b + a * b)

  b+ : ℕ → ℕ
  b+ = _+_ b

  +a*c : ℕ → ℕ
  +a*c = _+'_ (a * c)

  [b+c]+ : ℕ → ℕ
  [b+c]+ = _+_ (b + c)

  [𝕤a*[b+c]≡[b+c]+a*[b+c]] : (𝕤 a) * (b + c) ≡ (b + c) + a * (b + c)
  [𝕤a*[b+c]≡[b+c]+a*[b+c]] = ⟲ ((b + c) + a * (b + c))
 
  [[b+c]+a*[b+c]≡[b+c]+[a*b+a*c]] : (𝕤 a) * (b + c) ≡ (b + c) + (a * b + a * c)
  [[b+c]+a*[b+c]≡[b+c]+[a*b+a*c]] = [f≡g]→[fa≡ga]₂ [b+c]+ [b+c]+ (⟲ [b+c]+) (a * (b + c)) (a * b + a * c) [a*[b+c]≡a*b+a*c] 

  [𝕤a*b≡b+a*b] : (𝕤 a) * b ≡ b + a * b
  [𝕤a*b≡b+a*b] = ⟲ (b + a * b)

  [𝕤a*c≡c+a*c] : (𝕤 a) * c ≡ c + a * c
  [𝕤a*c≡c+a*c] = ⟲ (c + a * c)

  [𝕤a*b+𝕤a*c≡[b+a*b]+𝕤a*c] : (𝕤 a) * b + (𝕤 a) * c ≡ ( b + a * b) + (𝕤 a) * c
  [𝕤a*b+𝕤a*c≡[b+a*b]+𝕤a*c] = [f≡g]→[fa≡ga]₂ +𝕤a*c +𝕤a*c (⟲ +𝕤a*c) ((𝕤 a) * b) (b + a * b) [𝕤a*b≡b+a*b]

  [[b+a*b]+𝕤a*c≡[b+a*b]+[c+a*c]] : (b + a * b) + (𝕤 a) * c ≡ (b + a * b) + (c + a * c)
  [[b+a*b]+𝕤a*c≡[b+a*b]+[c+a*c]] = [f≡g]→[fa≡ga]₂ [b+a*b]+ [b+a*b]+ (⟲ [b+a*b]+) ((𝕤 a) * c) (c + a * c) [𝕤a*c≡c+a*c]

  [[b+a*b]+[c+a*c]≡b+[a*b+[c+a*c]]] : (b + a * b) + (c + a * c) ≡ b + (a * b + (c + a * c))
  [[b+a*b]+[c+a*c]≡b+[a*b+[c+a*c]]] = [a+b]+c≡a+[b+c] b (a * b) (c + a * c)

  [a*b+[c+a*c]]≡[a*b+c]+a*c] : a * b + (c + a * c) ≡ (a * b + c) + a * c
  [a*b+[c+a*c]]≡[a*b+c]+a*c] = ≡-↑↓ ([a+b]+c≡a+[b+c] (a * b) c (a * c))
 
  [a*b+c≡c+a*b] : a * b + c ≡ c + a * b
  [a*b+c≡c+a*b] = x+y≡y+x (a * b) c

  [[a*b+c]+a*c≡[c+a*b]+a*c] : (a * b + c) + a * c ≡ (c + a * b) + a * c
  [[a*b+c]+a*c≡[c+a*b]+a*c] = [f≡g]→[fa≡ga]₂ +a*c +a*c (⟲ +a*c) (a * b + c) (c + a * b) [a*b+c≡c+a*b]
  
  [[c+a*b]+a*c≡c+[a*b+a*c]] : (c + a * b) + a * c ≡ c + (a * b + a * c)
  [[c+a*b]+a*c≡c+[a*b+a*c]] = [a+b]+c≡a+[b+c] c (a * b) (a * c) 

  [a*b+[c+a*c]≡c+[a*b+a*c]] : a * b + (c + a * c) ≡ c + (a * b + a * c)
  [a*b+[c+a*c]≡c+[a*b+a*c]] = ≡-⇶ [a*b+[c+a*c]]≡[a*b+c]+a*c] (≡-⇶ [[a*b+c]+a*c≡[c+a*b]+a*c] [[c+a*b]+a*c≡c+[a*b+a*c]])

  [b+[a*b+[c+a*c]]≡b+[c+[a*b+a*c]]] : b + (a * b + (c + a * c)) ≡ b + (c + (a * b + a * c))
  [b+[a*b+[c+a*c]]≡b+[c+[a*b+a*c]]] = [f≡g]→[fa≡ga]₂ b+ b+ (⟲ b+) (a * b + (c + a * c)) (c + (a * b + a * c)) [a*b+[c+a*c]≡c+[a*b+a*c]]

  [b+[c+[a*b+a*c]]≡[b+c]+[a*b+a*c]] : b + (c + (a * b + a * c)) ≡ (b + c) + (a * b + a * c)
  [b+[c+[a*b+a*c]]≡[b+c]+[a*b+a*c]] = ≡-↑↓ ([a+b]+c≡a+[b+c] b c (a * b + a * c))

  [𝕤a*[b+c]≡𝕤a*b+𝕤a*c] : (𝕤 a) * (b + c) ≡ (𝕤 a) * b + (𝕤 a) * c
  [𝕤a*[b+c]≡𝕤a*b+𝕤a*c] = 
    ≡-⇶ [𝕤a*[b+c]≡[b+c]+a*[b+c]] 
   (≡-⇶ [[b+c]+a*[b+c]≡[b+c]+[a*b+a*c]]
   (≡-↑↓ (≡-⇶ [𝕤a*b+𝕤a*c≡[b+a*b]+𝕤a*c] 
         (≡-⇶ [[b+a*b]+𝕤a*c≡[b+a*b]+[c+a*c]]
         (≡-⇶ [[b+a*b]+[c+a*c]≡b+[a*b+[c+a*c]]]
         (≡-⇶ [b+[a*b+[c+a*c]]≡b+[c+[a*b+a*c]]]
               [b+[c+[a*b+a*c]]≡[b+c]+[a*b+a*c]]
         ))))))


-- final step
a*[b+c]≡a*b+a*c : (a b c : ℕ) → a * (b + c) ≡ a * b + a * c
a*[b+c]≡a*b+a*c 0 b c = 1-5-base<a,0> b c
a*[b+c]≡a*b+a*c (𝕤 a) b c = 1-5-ind<a,𝕤> a b c (a*[b+c]≡a*b+a*c a b c)


-- 6) Multiplication right-distributes over addition
-- a,b=0 base case
[0+0]*c≡0*c+0*c : (c : ℕ) → (0 + 0) * c ≡ 0 * c + 0 * c
[0+0]*c≡0*c+0*c c = ⟲ 0

-- a=0 base case
[0+𝕤b]*c≡0*c+𝕤b*c : (b c : ℕ) → (0 + (𝕤 b)) * c ≡ 0 * c + (𝕤 b) * c
[0+𝕤b]*c≡0*c+𝕤b*c b c = [[0+𝕤b]*c≡0*c+𝕤b*c]
 where
  *c : ℕ → ℕ
  *c = _*'_ c

  +𝕤b*c : ℕ → ℕ
  +𝕤b*c = _+'_ ((𝕤 b) * c)

  [0+𝕤b≡𝕤b] : 0 + (𝕤 b) ≡ (𝕤 b)
  [0+𝕤b≡𝕤b] = 𝕫+x≡x (𝕤 b)

  [0*c≡0] : 0 * c ≡ 0
  [0*c≡0] = 0*x≡0 c
 
  [0*c+𝕤b*c≡0+𝕤b*c] : 0 * c + (𝕤 b) * c ≡ 0 + (𝕤 b) * c
  [0*c+𝕤b*c≡0+𝕤b*c] = [a≡b]→[fa≡fb] +𝕤b*c (0 * c) 0 [0*c≡0]

  [0+𝕤b*c≡𝕤b*c] : 0 + (𝕤 b) * c ≡ (𝕤 b) * c
  [0+𝕤b*c≡𝕤b*c] = 𝕫+x≡x ((𝕤 b) * c)
 
  [[0+𝕤b]*c≡𝕤b*c] : (0 + (𝕤 b)) * c ≡ (𝕤 b) * c
  [[0+𝕤b]*c≡𝕤b*c] = [a≡b]→[fa≡fb] *c (0 + (𝕤 b)) (𝕤 b) [0+𝕤b≡𝕤b]

    

  [[0+𝕤b]*c≡0*c+𝕤b*c] : (0 + (𝕤 b)) * c ≡ 0 * c + (𝕤 b) * c
  [[0+𝕤b]*c≡0*c+𝕤b*c] = ≡-⇶ [[0+𝕤b]*c≡𝕤b*c] (≡-↑↓ (≡-⇶ [0*c+𝕤b*c≡0+𝕤b*c] [0+𝕤b*c≡𝕤b*c]))

-- b=0 base case
[𝕤a+0]*c≡𝕤a*c+0*c : (a c : ℕ) → ((𝕤 a) + 0) * c ≡ (𝕤 a) * c + 0 * c
[𝕤a+0]*c≡𝕤a*c+0*c a c = [[𝕤a+0]*c≡𝕤a*c+0*c]
 where
  𝕤a*c+ : ℕ → ℕ
  𝕤a*c+ = _+_ ((𝕤 a) * c)

  *c : ℕ → ℕ
  *c = _*'_ c

  [0*c≡0] : 0 * c ≡ 0
  [0*c≡0] = 0*x≡0 c
 
  [𝕤a*c+0*c≡𝕤a*c+0] : (𝕤 a) * c + 0 * c ≡ (𝕤 a) * c + 0
  [𝕤a*c+0*c≡𝕤a*c+0] = [a≡b]→[fa≡fb] 𝕤a*c+ (0 * c) 0 [0*c≡0]

  [𝕤a*c+0≡𝕤a*c] : (𝕤 a) * c + 0 ≡ (𝕤 a) * c
  [𝕤a*c+0≡𝕤a*c] = x+𝕫≡x ((𝕤 a) * c)

  [𝕤a+0≡𝕤a] : (𝕤 a) + 0 ≡ (𝕤 a)
  [𝕤a+0≡𝕤a] = x+𝕫≡x (𝕤 a)

  [[𝕤a+0]*c≡𝕤a*c] : ((𝕤 a) + 0) * c ≡ (𝕤 a) * c
  [[𝕤a+0]*c≡𝕤a*c] = [a≡b]→[fa≡fb] *c ((𝕤 a) + 0) (𝕤 a) [𝕤a+0≡𝕤a]

  [[𝕤a+0]*c≡𝕤a*c+0*c] : ((𝕤 a) + 0) * c ≡ (𝕤 a) * c + 0 * c
  [[𝕤a+0]*c≡𝕤a*c+0*c] = ≡-⇶ [[𝕤a+0]*c≡𝕤a*c] (≡-↑↓ (≡-⇶ [𝕤a*c+0*c≡𝕤a*c+0] [𝕤a*c+0≡𝕤a*c]))

-- ab-inductive
[[a+b]*c≡a*c+b*c]→[[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] : 
 (a b c : ℕ) → (a + b) * c ≡ a * c + b * c → ((𝕤 a) + (𝕤 b)) * c ≡ (𝕤 a) * c + (𝕤 b) * c
[[a+b]*c≡a*c+b*c]→[[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] a b c [[a+b]*c≡a*c+b*c] = [[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c]
 where

  *c : ℕ → ℕ
  *c = _*'_ c

  [c+c]+ : ℕ → ℕ
  [c+c]+ = _+_ (c + c)
  
  +b*c : ℕ → ℕ
  +b*c = _+'_ (b * c)

  c+ : ℕ → ℕ
  c+ = _+_ c
--

  [𝕤a*c≡c+a*c] : (𝕤 a) * c ≡  c + (a * c)
  [𝕤a*c≡c+a*c] = ⟲ (c + a * c)

  [𝕤b*c≡c+b*c] : (𝕤 b) * c ≡  c + (b * c)
  [𝕤b*c≡c+b*c] = ⟲ (c + b * c)

  [𝕤a*c+𝕤b*c≡[c+a*c]+[c+b*c]] : (𝕤 a) * c + (𝕤 b) * c ≡ (c + a * c) + (c + b * c)
  [𝕤a*c+𝕤b*c≡[c+a*c]+[c+b*c]] = ⟲ ((c + a * c) + (c + b * c))

  [𝕤a+𝕤b≡𝕤[a+𝕤b]] : (𝕤 a) + (𝕤 b) ≡ 𝕤 (a + (𝕤 b))
  [𝕤a+𝕤b≡𝕤[a+𝕤b]] = 𝕤x+y≡𝕤[x+y] a (𝕤 b)
 
  [a+𝕤b≡𝕤[a+b]] : a + (𝕤 b) ≡ (𝕤 ( a + b))
  [a+𝕤b≡𝕤[a+b]] = x+𝕤y≡𝕤[x+y] a b

  [𝕤[a+𝕤b]≡𝕤𝕤[a+b]] : (𝕤 (a + (𝕤 b))) ≡ (𝕤 (𝕤 (a + b)))
  [𝕤[a+𝕤b]≡𝕤𝕤[a+b]] = [a≡b]→[fa≡fb] 𝕤 (a + (𝕤 b)) (𝕤 (a + b)) [a+𝕤b≡𝕤[a+b]]

  [𝕤a+𝕤b≡𝕤𝕤[a+b]] : (𝕤 a) + (𝕤 b) ≡ (𝕤 (𝕤 (a + b)))
  [𝕤a+𝕤b≡𝕤𝕤[a+b]] = ≡-⇶ [𝕤a+𝕤b≡𝕤[a+𝕤b]] [𝕤[a+𝕤b]≡𝕤𝕤[a+b]]

  [[𝕤a+𝕤b]*c≡[𝕤𝕤[a+b]]*c] : ((𝕤 a) + (𝕤 b)) * c ≡ (𝕤 (𝕤 (a + b))) * c
  [[𝕤a+𝕤b]*c≡[𝕤𝕤[a+b]]*c] = [a≡b]→[fa≡fb] *c ((𝕤 a) + (𝕤 b)) (𝕤 (𝕤 (a + b))) [𝕤a+𝕤b≡𝕤𝕤[a+b]]

  [[𝕤𝕤[a+b]]*c≡c+[c+[a+b]*c]] : (𝕤 (𝕤 (a + b))) * c ≡ c + (c + (a + b) * c)
  [[𝕤𝕤[a+b]]*c≡c+[c+[a+b]*c]] = ⟲ (c + (c + (a + b) * c))

  [c+[c+[a+b]*c]≡[c+c]+[a+b]*c] : c + (c + (a + b) * c) ≡ (c + c) + (a + b) * c  
  [c+[c+[a+b]*c]≡[c+c]+[a+b]*c] = ≡-↑↓ ([a+b]+c≡a+[b+c] c c ((a + b) * c))

  [[c+c]+[a+b]*c≡[c+c]+[a*c+b*c]] : (c + c) + (a + b) * c ≡ (c + c) + (a * c + b * c)
  [[c+c]+[a+b]*c≡[c+c]+[a*c+b*c]] = [a≡b]→[fa≡fb] [c+c]+ ((a + b) * c) (a * c + b * c) [[a+b]*c≡a*c+b*c]

  [[c+c]+[a*c+b*c]≡c+[c+[a*c+b*c]]] : (c + c) + (a * c + b * c) ≡ c + (c + (a * c + b * c))
  [[c+c]+[a*c+b*c]≡c+[c+[a*c+b*c]]] = [a+b]+c≡a+[b+c] c c (a * c + b * c)

  [c+[a*c+b*c]≡[c+a*c]+b*c] : c + (a * c + b * c) ≡ (c + a * c) + b * c
  [c+[a*c+b*c]≡[c+a*c]+b*c] = ≡-↑↓ ([a+b]+c≡a+[b+c] c (a * c) (b * c))

  [c+a*c≡a*c+c] : c + a * c ≡ a * c + c
  [c+a*c≡a*c+c] = x+y≡y+x c (a * c)

  [[c+a*c]+b*c≡[a*c+c]+b*c] : (c + a * c) + b * c ≡ (a * c + c) + b * c
  [[c+a*c]+b*c≡[a*c+c]+b*c] = [a≡b]→[fa≡fb] +b*c (c + a * c) (a * c + c) [c+a*c≡a*c+c]

  [[a*c+c]+b*c≡a*c+[c+b*c]] : (a * c + c) + b * c ≡ a * c + (c + b * c)
  [[a*c+c]+b*c≡a*c+[c+b*c]] = [a+b]+c≡a+[b+c] (a * c) c (b * c)

  [c+[a*c+b*c]≡a*c+[c+b*c]] : c + (a * c + b * c) ≡ a * c + (c + b * c)
  [c+[a*c+b*c]≡a*c+[c+b*c]] = ≡-⇶ [c+[a*c+b*c]≡[c+a*c]+b*c] (≡-⇶ [[c+a*c]+b*c≡[a*c+c]+b*c] [[a*c+c]+b*c≡a*c+[c+b*c]])

  [c+[c+[a*c+b*c]]≡c+[a*c+[c+b*c]]] : c + (c + (a * c + b * c)) ≡ c + (a * c + (c + b * c))
  [c+[c+[a*c+b*c]]≡c+[a*c+[c+b*c]]] = [a≡b]→[fa≡fb] c+ (c + (a * c + b * c)) (a * c + (c + b * c)) [c+[a*c+b*c]≡a*c+[c+b*c]]

  [c+[a*c+[c+b*c]]≡[c+a*c]+[c+b*c]] : c + (a * c + (c + b * c)) ≡ (c + a * c) + (c + b * c)
  [c+[a*c+[c+b*c]]≡[c+a*c]+[c+b*c]] = ≡-↑↓ ([a+b]+c≡a+[b+c] c (a * c) (c + b * c)) 

  [[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] : ((𝕤 a) + (𝕤 b)) * c ≡ (𝕤 a) * c + (𝕤 b) * c
  [[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] = ≡-⇶ [[𝕤a+𝕤b]*c≡[𝕤𝕤[a+b]]*c] 
                          (≡-⇶ [[𝕤𝕤[a+b]]*c≡c+[c+[a+b]*c]]
                          (≡-⇶ [c+[c+[a+b]*c]≡[c+c]+[a+b]*c]
                          (≡-⇶ [[c+c]+[a+b]*c≡[c+c]+[a*c+b*c]]
                          (≡-⇶ [[c+c]+[a*c+b*c]≡c+[c+[a*c+b*c]]]
                          (≡-⇶ [c+[c+[a*c+b*c]]≡c+[a*c+[c+b*c]]]
                          (≡-⇶ [c+[a*c+[c+b*c]]≡[c+a*c]+[c+b*c]]
                          (≡-↑↓ [𝕤a*c+𝕤b*c≡[c+a*c]+[c+b*c]])))))))


-- final step
[a+b]*c≡a*c+b*c : (a b c : ℕ) → (a + b) * c ≡ a * c + b * c
[a+b]*c≡a*c+b*c 0 0 = [0+0]*c≡0*c+0*c
[a+b]*c≡a*c+b*c (𝕤 a) 0 = [𝕤a+0]*c≡𝕤a*c+0*c a
[a+b]*c≡a*c+b*c 0 (𝕤 b) = [0+𝕤b]*c≡0*c+𝕤b*c b
[a+b]*c≡a*c+b*c (𝕤 a) (𝕤 b) c = [[a+b]*c≡a*c+b*c]→[[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] a b c ([a+b]*c≡a*c+b*c a b c)











-- 7) Lemma: (a * x ) * y ≡ x * (a * y)
-- base case
[0*x]*y≡x*[0*y] : (x y : ℕ) → (0 * x) * y ≡ x * (0 * y)
[0*x]*y≡x*[0*y] x y = [[0*x]*y≡x*[0*y]]
 where
-- Defs :
  *y : ℕ → ℕ
  *y = _*'_ y

  x* : ℕ → ℕ
  x* = _*_ x

  [0*x≡0] : 0 * x ≡ 0
  [0*x≡0] = 0*x≡0 x

  [0*y≡0] : 0 * y ≡ 0
  [0*y≡0] = 0*x≡0 y
 
  [[0*x]*y≡0*y] : (0 * x) * y ≡ 0 * y
  [[0*x]*y≡0*y] = [f≡g]→[fa≡ga]₂ *y *y (⟲ *y) (0 * x) 0 [0*x≡0]

  [[0*x]*y≡0] : (0 * x) * y ≡ 0
  [[0*x]*y≡0] = ≡-⇶ [[0*x]*y≡0*y] [0*y≡0]

  [x*0≡x*[0*y]] : x * 0 ≡ x * (0 * y)
  [x*0≡x*[0*y]] = [f≡g]→[fa≡ga]₂ x* x* (⟲ x*) 0 (0 * y) (≡-↑↓ [0*y≡0])

  [0≡x*0] : 0 ≡ x * 0
  [0≡x*0] = ≡-↑↓ (x*0≡0 x)

  [0≡x*[0*y]] : 0 ≡ x * (0 * y)
  [0≡x*[0*y]] = ≡-⇶ [0≡x*0] [x*0≡x*[0*y]]

  [[0*x]*y≡x*[0*y]] : (0 * x) * y ≡ x * (0 * y)
  [[0*x]*y≡x*[0*y]] = ≡-⇶ [[0*x]*y≡0] [0≡x*[0*y]]
  

-- inductive step
[[a*x]*y≡x*[a*y]]-ind<𝕤,a> :
 (x y a : ℕ) → (a * x) * y ≡ x * (a * y) → ((𝕤 a) * x) * y ≡ x * ((𝕤 a) * y)
[[a*x]*y≡x*[a*y]]-ind<𝕤,a> x y a [[a*x]*y≡x*[a*y]] = [[𝕤a*x]*y≡x*[𝕤a*y]]
 where
  x* : ℕ → ℕ
  x* = _*_ x

  *y : ℕ → ℕ
  *y = _*'_ y
  
  x*y+ : ℕ → ℕ
  x*y+ = _+_ (x * y)

--
  [𝕤a*x≡x+a*x] : (𝕤 a) * x ≡ x + a * x
  [𝕤a*x≡x+a*x] = ⟲ (x + a * x)

  [𝕤a*y≡y+a*y] : (𝕤 a) * y ≡ y + a * y
  [𝕤a*y≡y+a*y] = ⟲ (y + a * y)

  [x*[𝕤a*y]≡x*[y+a*y]] : x * ((𝕤 a) * y) ≡ x * (y + a * y)
  [x*[𝕤a*y]≡x*[y+a*y]] = [f≡g]→[fa≡ga]₂ x* x* (⟲ x*) ((𝕤 a) * y) (y + a * y) [𝕤a*y≡y+a*y]

  [x*[y+a*y]≡x*y+x*[a*y]] : x * (y + a * y) ≡ x * y + x * (a * y)
  [x*[y+a*y]≡x*y+x*[a*y]] = a*[b+c]≡a*b+a*c x y (a * y)

  [[𝕤a*x]*y≡[x+a*x]*y] : ((𝕤 a) * x) * y ≡ (x + a * x) * y
  [[𝕤a*x]*y≡[x+a*x]*y] = [f≡g]→[fa≡ga]₂ *y *y (⟲ *y) ((𝕤 a) * x) (x + a * x) [𝕤a*x≡x+a*x]

  [[x+a*x]*y≡x*y+[a*x]*y] : (x + a * x) * y ≡ x * y + (a * x) * y
  [[x+a*x]*y≡x*y+[a*x]*y] = [a+b]*c≡a*c+b*c x (a * x) y

  [x*y+x*[a*y]≡x*y+[a*x]*y] : x * y + x * (a * y) ≡ x * y + (a * x) * y
  [x*y+x*[a*y]≡x*y+[a*x]*y] = [a≡b]→[fa≡fb] x*y+ (x * (a * y)) ((a * x) * y) (≡-↑↓ [[a*x]*y≡x*[a*y]])

  [[𝕤a*x]*y≡x*[𝕤a*y]] : ((𝕤 a) * x) * y ≡ x * ((𝕤 a) * y)
  [[𝕤a*x]*y≡x*[𝕤a*y]] = ≡-⇶ [[𝕤a*x]*y≡[x+a*x]*y]
                       (≡-⇶ [[x+a*x]*y≡x*y+[a*x]*y]
                        (≡-↑↓ (≡-⇶ [x*[𝕤a*y]≡x*[y+a*y]] 
                              (≡-⇶ [x*[y+a*y]≡x*y+x*[a*y]]
                                     [x*y+x*[a*y]≡x*y+[a*x]*y]
                              ))))


-- final step
[a*x]*y≡x*[a*y] : (x y a : ℕ) → (a * x) * y ≡ x * (a * y)
[a*x]*y≡x*[a*y] x y 0 = [0*x]*y≡x*[0*y] x y
[a*x]*y≡x*[a*y] x y (𝕤 a) = [[a*x]*y≡x*[a*y]]-ind<𝕤,a> x y a ([a*x]*y≡x*[a*y] x y a)





-- 8) Multiplication is commutative
x*y≡y*x : (x y : ℕ) → x * y ≡ y * x
x*y≡y*x x y = [x*y≡y*x]
 where
  y* : ℕ → ℕ
  y* = _*_ y

  [[x*y]*1≡y*[x*1]] : (x * y) * 1 ≡ y * (x * 1)
  [[x*y]*1≡y*[x*1]] = [a*x]*y≡x*[a*y] y 1 x

  [[x*y]*1≡x*y] : (x * y) * 1 ≡ x * y
  [[x*y]*1≡x*y] = x*1≡x (x * y)

  [x*1≡x] : x * 1 ≡ x
  [x*1≡x] = x*1≡x x

  [y*[x*1]≡y*x] : y * (x * 1) ≡ y * x
  [y*[x*1]≡y*x] = [a≡b]→[fa≡fb] y* (x * 1) x [x*1≡x]

  [x*y≡y*x] : x * y ≡ y * x
  [x*y≡y*x] = ≡-⇶ (≡-↑↓ [[x*y]*1≡x*y]) (≡-⇶ [[x*y]*1≡y*[x*1]] [y*[x*1]≡y*x])



-- 9) (a * b) * c ≡ a * (b * c)  ; Multiplication is associative
[a*b]*c≡a*[b*c] : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
[a*b]*c≡a*[b*c] a b c = [[a*b]*c≡a*[b*c]]
 where
  *c : ℕ → ℕ
  *c = _*'_ c
--
  [a*b≡b*a] : a * b ≡ b * a
  [a*b≡b*a] = x*y≡y*x a b

  [[a*b]*c≡[b*a]*c] : (a * b) * c ≡ (b * a) * c
  [[a*b]*c≡[b*a]*c] = [a≡b]→[fa≡fb] *c (a * b) (b * a) [a*b≡b*a]

  [[b*a]*c≡a*[b*c]] : (b * a) * c ≡ a * (b * c)
  [[b*a]*c≡a*[b*c]] = [a*x]*y≡x*[a*y] a c b

  [[a*b]*c≡a*[b*c]] : (a * b) * c ≡ a * (b * c)
  [[a*b]*c≡a*[b*c]] = ≡-⇶ [[a*b]*c≡[b*a]*c] [[b*a]*c≡a*[b*c]]








-- difference

-- 1) diff x x ≡ 𝕫
-- 2) diff 𝕤x 𝕤y ≡ diff x y
-- 3) diff 𝕫 x ≡ x
-- 4) diff x 𝕫 ≡ x
-- 5) diff x y ≡ diff y x


-- 1) diff x x ≡ 𝕫
-- base case for diff x x ≡ 𝕫
diff-𝕫-𝕫≡𝕫 : diff 𝕫 𝕫 ≡ 𝕫
diff-𝕫-𝕫≡𝕫 = ⟲ 𝕫

-- inductive step for diff x x ≡ 𝕫
[diff-x-x≡𝕫]→[diff-𝕤x-𝕤x≡𝕫] : (x : ℕ) → diff x x ≡ 𝕫 → diff (𝕤 x) (𝕤 x) ≡ 𝕫
[diff-x-x≡𝕫]→[diff-𝕤x-𝕤x≡𝕫] x [diff-x-x≡𝕫] = [diff-𝕤x-𝕤x≡𝕫]
 where
  [diff-𝕤x-𝕤x≡diff-x-x] : diff (𝕤 x) (𝕤 x) ≡ diff x x
  [diff-𝕤x-𝕤x≡diff-x-x] = ⟲ (diff x x)

  [diff-𝕤x-𝕤x≡𝕫] :  diff (𝕤 x) (𝕤 x) ≡ 𝕫
  [diff-𝕤x-𝕤x≡𝕫] = ≡-⇶ [diff-𝕤x-𝕤x≡diff-x-x] [diff-x-x≡𝕫]

--final step for diff x x ≡ 𝕫
diff-x-x≡𝕫 : (x : ℕ) → diff x x ≡ 𝕫
diff-x-x≡𝕫 𝕫 = diff-𝕫-𝕫≡𝕫
diff-x-x≡𝕫 (𝕤 x) = [diff-x-x≡𝕫]→[diff-𝕤x-𝕤x≡𝕫] x (diff-x-x≡𝕫 x)

𝕫≡diff-x-x : (x : ℕ) → 𝕫 ≡ diff x x
𝕫≡diff-x-x x = ≡-↑↓ (diff-x-x≡𝕫 x)


-- 2) diff 𝕤x 𝕤y ≡ diff x y
diff-𝕤x-𝕤y≡diff-x-y : (x y : ℕ) → diff (𝕤 x) (𝕤 y) ≡ diff x y
diff-𝕤x-𝕤y≡diff-x-y x y = ⟲ (diff x y)

diff-x-y≡diff-𝕤x-𝕤y : (x y : ℕ) → diff x y ≡ diff (𝕤 x) (𝕤 y)
diff-x-y≡diff-𝕤x-𝕤y x y = ⟲ (diff x y)


-- 3) diff 𝕫 x ≡ x
diff-𝕫-x≡x : (x : ℕ) → diff 𝕫 x ≡ x
diff-𝕫-x≡x x = ⟲ x

x≡diff-𝕫-x : (x : ℕ) → x ≡ diff 𝕫 x
x≡diff-𝕫-x x = ⟲ x


-- 4) diff x 𝕫 ≡ x
-- lemma
diff-𝕤x-𝕫≡𝕤x : (x : ℕ) → diff (𝕤 x) 𝕫 ≡ (𝕤 x)
diff-𝕤x-𝕫≡𝕤x x = ⟲ (𝕤 x)

-- inductive step for diff-x-𝕫≡x
[diff-x-𝕫≡x]→[diff-𝕤x-𝕫≡𝕤x] : (x : ℕ) → diff x 𝕫 ≡ x → diff (𝕤 x) 𝕫 ≡ (𝕤 x)
[diff-x-𝕫≡x]→[diff-𝕤x-𝕫≡𝕤x] x [diff-x-𝕫≡x] = diff-𝕤x-𝕫≡𝕤x x

-- final step for diff-x-𝕫≡x
diff-x-𝕫≡x : (x : ℕ) → diff x 𝕫 ≡ x
diff-x-𝕫≡x 𝕫 = diff-𝕫-𝕫≡𝕫
diff-x-𝕫≡x (𝕤 x) = [diff-x-𝕫≡x]→[diff-𝕤x-𝕫≡𝕤x] x (diff-x-𝕫≡x x)

x≡diff-x-𝕫 : (x : ℕ) → x ≡ diff x 𝕫
x≡diff-x-𝕫 x = ≡-↑↓ (diff-x-𝕫≡x x)



-- 5) diff x y ≡ diff y x
-- xy-base 
diff-0-0≡diff-0-0 : diff 0 0 ≡ diff 0 0
diff-0-0≡diff-0-0 = ⟲ (diff 0 0)

-- y-base
diff-𝕤x-0≡diff-0-𝕤x : (x : ℕ) → diff (𝕤 x) 0 ≡ diff 0 (𝕤 x)
diff-𝕤x-0≡diff-0-𝕤x x = ⟲ (𝕤 x)

-- x-base
diff-0-𝕤y≡diff-𝕤y-0 : (y : ℕ) → diff 0 (𝕤 y) ≡ diff (𝕤 y) 0
diff-0-𝕤y≡diff-𝕤y-0 y = ⟲ (𝕤 y)

-- xy-induction
[diff-x-y≡diff-y-x]→[diff-𝕤x-𝕤y≡diff-𝕤y-𝕤x] : (x y : ℕ) → diff x y ≡ diff y x → diff (𝕤 x) (𝕤 y) ≡ diff (𝕤 y) (𝕤 x)
[diff-x-y≡diff-y-x]→[diff-𝕤x-𝕤y≡diff-𝕤y-𝕤x] x y [diff-x-y≡diff-y-x] = [diff-𝕤x-𝕤y≡diff-𝕤y-𝕤x]
 where
  [diff-𝕤x-𝕤y≡diff-x-y] : diff (𝕤 x) (𝕤 y) ≡ diff x y
  [diff-𝕤x-𝕤y≡diff-x-y] = ⟲ (diff x y)

  [diff-y-x≡diff-𝕤y-𝕤x] : diff y x ≡ diff (𝕤 y) (𝕤 x)
  [diff-y-x≡diff-𝕤y-𝕤x] = ⟲ (diff y x)


  [diff-𝕤x-𝕤y≡diff-𝕤y-𝕤x] : diff (𝕤 x) (𝕤 y) ≡ diff (𝕤 y) (𝕤 x)
  [diff-𝕤x-𝕤y≡diff-𝕤y-𝕤x] = ≡-⇶ [diff-𝕤x-𝕤y≡diff-x-y] (≡-⇶ [diff-x-y≡diff-y-x] [diff-y-x≡diff-𝕤y-𝕤x])

-- final step
diff-x-y≡diff-y-x : (x y : ℕ) → diff x y ≡ diff y x
diff-x-y≡diff-y-x 0 0 = diff-0-0≡diff-0-0
diff-x-y≡diff-y-x (𝕤 x) 0 = diff-𝕤x-0≡diff-0-𝕤x x
diff-x-y≡diff-y-x 0 (𝕤 y) = diff-0-𝕤y≡diff-𝕤y-0 y
diff-x-y≡diff-y-x (𝕤 x) (𝕤 y) = [diff-x-y≡diff-y-x]→[diff-𝕤x-𝕤y≡diff-𝕤y-𝕤x] x y (diff-x-y≡diff-y-x x y)










-- gte
{-
 So we have propositions like "x ≥ y" , but then we have algorithms like "gte"
 which computes a boolean value intended to indicate whether "x ≥ y" is actually
 true. So we'd like to be able to say that there's a bi-implication "x gte y ≡ 𝕥" 
 and "x ≥ y"
-}


-- 1) If x gte y, then y + (diff x y) ≡ x
-- 2) If x gte y ≡ 𝕥 , then x ≥ y.
-- 3) If x ≥ y , then x gte y ≡ 𝕥. 




-- 1) If x gte y then y+(diff x y)≡x

-- xy-base  
[0-gte-0]→[0+[diff-0-0]≡0] : 0 gte 0 ≡ 𝕥 → 0 + (diff 0 0) ≡ 0
[0-gte-0]→[0+[diff-0-0]≡0] [0-gte-0≡𝕥] = ⟲ 0

-- y-base
[𝕤x-gte-0]→[0+[diff-𝕤x-0]≡𝕤x] : (x : ℕ) → (𝕤 x) gte 0 ≡ 𝕥 → 0 + (diff (𝕤 x) 0) ≡ (𝕤 x)
[𝕤x-gte-0]→[0+[diff-𝕤x-0]≡𝕤x] x [𝕤x-gte-0≡𝕥] = ⟲ (𝕤 x)

-- x-base
[0-gte-𝕤y]→[𝕤y+[diff-0-𝕤y]≡0] : (y : ℕ) → 0 gte (𝕤 y) ≡ 𝕥 → (𝕤 y) + (diff 0 (𝕤 y)) ≡ 0
[0-gte-𝕤y]→[𝕤y+[diff-0-𝕤y]≡0] y [0-gte-𝕤y≡𝕥] = [𝕤y+[diff-0-𝕤y]≡0]
 where
  [𝕗≡0-gte-𝕤y] : 𝕗 ≡ 0 gte (𝕤 y)
  [𝕗≡0-gte-𝕤y] = ⟲ 𝕗

  [𝕗≡𝕥] : 𝕗 ≡ 𝕥
  [𝕗≡𝕥] = ≡-⇶ [𝕗≡0-gte-𝕤y] [0-gte-𝕤y≡𝕥]

  ☢ : ⊥
  ☢ = 𝕗≠𝕥 [𝕗≡𝕥]

  [𝕤y+[diff-0-𝕤y]≡0] : (𝕤 y) + (diff 0 (𝕤 y)) ≡ 0
  [𝕤y+[diff-0-𝕤y]≡0] = ω ☢

-- xy-induction
[[x-gte-y]→[y+[diff-x-y]≡x]-ind-xy : 
 (x y : ℕ) → (x gte y ≡ 𝕥 → y + (diff x y) ≡ x) → 
 (𝕤 x) gte (𝕤 y) ≡ 𝕥 → (𝕤 y) + (diff (𝕤 x) (𝕤 y)) ≡ (𝕤 x)
[[x-gte-y]→[y+[diff-x-y]≡x]-ind-xy 
 x y [[x-gte-y]→[y+[diff-x-y]≡x] [𝕤x-gte-𝕤y≡𝕥] = [𝕤y+[diff-𝕤x-𝕤y]≡𝕤x]
  where
-- Defs :
   𝕤y+ : ℕ → ℕ
   𝕤y+ = _+_ (𝕤 y)

   [x-gte-y≡𝕤x-gte-𝕤y] : x gte y ≡ (𝕤 x) gte (𝕤 y)
   [x-gte-y≡𝕤x-gte-𝕤y] = ⟲ (x gte y)
  
   [x-gte-y≡𝕥] : x gte y ≡ 𝕥
   [x-gte-y≡𝕥] = ≡-⇶ [x-gte-y≡𝕤x-gte-𝕤y] [𝕤x-gte-𝕤y≡𝕥]
  
   [y+[diff-x-y]≡x] : y + (diff x y) ≡ x
   [y+[diff-x-y]≡x] = [[x-gte-y]→[y+[diff-x-y]≡x] [x-gte-y≡𝕥]  

   [diff-𝕤x-𝕤y≡diff-x-y] : diff (𝕤 x) (𝕤 y) ≡ diff x y
   [diff-𝕤x-𝕤y≡diff-x-y] = ⟲ (diff x y)

   [𝕤y+[diff-𝕤x-𝕤y]≡𝕤y+[diff-x-y]] : (𝕤 y) + (diff (𝕤 x) (𝕤 y)) ≡ (𝕤 y) + (diff x y)
   [𝕤y+[diff-𝕤x-𝕤y]≡𝕤y+[diff-x-y]] = [f≡g]→[fa≡ga]₂ 𝕤y+ 𝕤y+ (⟲ 𝕤y+) (diff (𝕤 x) (𝕤 y)) (diff x y) [diff-𝕤x-𝕤y≡diff-x-y]

   [𝕤[y+[diff-x-y]]≡𝕤y+[diff-x-y]] : (𝕤 (y + (diff x y))) ≡ (𝕤 y) + (diff x y)
   [𝕤[y+[diff-x-y]]≡𝕤y+[diff-x-y]] = 𝕤[x+y]≡𝕤x+y y (diff x y)

   [𝕤[y+[diff-x-y]]≡𝕤x] : 𝕤 (y + (diff x y)) ≡ (𝕤 x)
   [𝕤[y+[diff-x-y]]≡𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (y + (diff x y)) x [y+[diff-x-y]≡x]

   [𝕤y+[diff-𝕤x-𝕤y]≡𝕤x] : (𝕤 y) + (diff (𝕤 x) (𝕤 y)) ≡ (𝕤 x)
   [𝕤y+[diff-𝕤x-𝕤y]≡𝕤x] = ≡-↑↓ (≡-⇶ (≡-↑↓ [𝕤[y+[diff-x-y]]≡𝕤x]) (≡-⇶ [𝕤[y+[diff-x-y]]≡𝕤y+[diff-x-y]] (≡-↑↓ [𝕤y+[diff-𝕤x-𝕤y]≡𝕤y+[diff-x-y]])))

-- final:
[x-gte-y]→[y+[diff-x-y]≡x] : (x y : ℕ) → x gte y ≡ 𝕥 →  y + (diff x y) ≡ x
[x-gte-y]→[y+[diff-x-y]≡x] 0 0 = [0-gte-0]→[0+[diff-0-0]≡0]
[x-gte-y]→[y+[diff-x-y]≡x] (𝕤 x) 0 = [𝕤x-gte-0]→[0+[diff-𝕤x-0]≡𝕤x] x
[x-gte-y]→[y+[diff-x-y]≡x] 0 (𝕤 y) = [0-gte-𝕤y]→[𝕤y+[diff-0-𝕤y]≡0] y
[x-gte-y]→[y+[diff-x-y]≡x] (𝕤 x) (𝕤 y) = [[x-gte-y]→[y+[diff-x-y]≡x]-ind-xy x y ([x-gte-y]→[y+[diff-x-y]≡x] x y)


-- 2) If x gte y ≡ 𝕥 , then x ≥ y.
[x-gte-y]→[x≥y] : (x y : ℕ) → x gte y ≡ 𝕥 → x ≥ y
[x-gte-y]→[x≥y] x y [x-gte-y≡𝕥] = ((diff x y) , [y+[diff-x-y]≡x])
 where
  [y+[diff-x-y]≡x] : y + (diff x y) ≡ x
  [y+[diff-x-y]≡x] = [x-gte-y]→[y+[diff-x-y]≡x] x y [x-gte-y≡𝕥]



-- 3) [x≥y]→[x-gte-y] ; If x ≥ y, then x gte y ≡ 𝕥.
-- xy-base
[0≥0]→[0-gte-0] : 0 ≥ 0 → 0 gte 0 ≡ 𝕥
[0≥0]→[0-gte-0] [0≥0] = ⟲ 𝕥

-- y-base
[𝕤x≥0]→[𝕤x-gte-0] : (x : ℕ) → (𝕤 x) ≥ 0 → (𝕤 x) gte 0 ≡ 𝕥
[𝕤x≥0]→[𝕤x-gte-0] x [𝕤x≥0] = ⟲ 𝕥

-- x-base
[0≥𝕤y]→[0-gte-𝕤y] : (y : ℕ) → 0 ≥ (𝕤 y) → 0 gte (𝕤 y) ≡ 𝕥
[0≥𝕤y]→[0-gte-𝕤y] y (a , [𝕤y+a≡0]) = [0-gte-𝕤y≡𝕥]
 where
  [𝕤[y+a]≡𝕤y+a] : (𝕤 (y + a)) ≡  (𝕤 y) + a
  [𝕤[y+a]≡𝕤y+a] = 𝕤[x+y]≡𝕤x+y y a  

  [𝕤[y+a]≡0] : (𝕤 (y + a)) ≡ 0
  [𝕤[y+a]≡0] = ≡-⇶ [𝕤[y+a]≡𝕤y+a] [𝕤y+a≡0]

  ☢ : ⊥
  ☢ = 𝕤x≠𝕫 (y + a) [𝕤[y+a]≡0]
  
  [0-gte-𝕤y≡𝕥] : 0 gte (𝕤 y) ≡ 𝕥
  [0-gte-𝕤y≡𝕥] = ω ☢

-- xy-induction
[[x≥y]→[x-gte-y]]-ind-xy :
  (x y : ℕ) → (x ≥ y → x gte y ≡ 𝕥) → (𝕤 x) ≥ (𝕤 y) → (𝕤 x) gte (𝕤 y) ≡ 𝕥
[[x≥y]→[x-gte-y]]-ind-xy
  x y [[x≥y]→[x-gte-y]] (a , [𝕤y+a≡𝕤x]) = [𝕤x-gte-𝕤y≡𝕥]
  where
   [𝕤[y+a]≡𝕤y+a] : (𝕤 (y + a)) ≡ (𝕤 y) + a
   [𝕤[y+a]≡𝕤y+a] = 𝕤[x+y]≡𝕤x+y y a

   [𝕤[y+a]≡𝕤x] : (𝕤 (y + a)) ≡ (𝕤 x)
   [𝕤[y+a]≡𝕤x] = ≡-⇶ [𝕤[y+a]≡𝕤y+a] [𝕤y+a≡𝕤x]

   [y+a≡x] : y + a ≡ x
   [y+a≡x] = [𝕤x≡𝕤y]→[x≡y] (y + a) x [𝕤[y+a]≡𝕤x]
  
   [x≥y] : x ≥ y
   [x≥y] = (a , [y+a≡x])

   [x-gte-y≡𝕥] : x gte y ≡ 𝕥
   [x-gte-y≡𝕥] = [[x≥y]→[x-gte-y]] [x≥y]

   [𝕤x-gte-𝕤y≡x-gte-y] : (𝕤 x) gte (𝕤 y) ≡ x gte y
   [𝕤x-gte-𝕤y≡x-gte-y] = ⟲ (x gte y)

   [𝕤x-gte-𝕤y≡𝕥] : (𝕤 x) gte (𝕤 y) ≡ 𝕥
   [𝕤x-gte-𝕤y≡𝕥] = ≡-⇶ [𝕤x-gte-𝕤y≡x-gte-y] [x-gte-y≡𝕥]

-- final step
[x≥y]→[x-gte-y] : (x y : ℕ) → x ≥ y → x gte y ≡ 𝕥
[x≥y]→[x-gte-y] 0 0 = [0≥0]→[0-gte-0]
[x≥y]→[x-gte-y] (𝕤 x) 0 = [𝕤x≥0]→[𝕤x-gte-0] x
[x≥y]→[x-gte-y] 0 (𝕤 y) = [0≥𝕤y]→[0-gte-𝕤y] y
[x≥y]→[x-gte-y] (𝕤 x) (𝕤 y) = [[x≥y]→[x-gte-y]]-ind-xy x y ([x≥y]→[x-gte-y] x y)




-- SECTION : lists
-- 1) Reversing twice is the identity

rev²-[]≡[] : ∀ {α} {A : ★ α} → list-reverse (list-reverse { α } { A } []) ≡ []
rev²-[]≡[] = ⟲ []

{-
rev²-[f::r] : ∀ {α} {A : ★ α} → (r : [ A ]) → (f : A) → list-reverse (list-reverse (f :: r)) ≡ (f :: r)
rev²-[f::r] {α} {A} r f = [rev²-[f::r]]
 where
  
  [rev²-[f::r]]
-}

rev-[f::[]]≡[f::[]] : ∀ {α} {A : ★ α} (f : A) → list-reverse (f :: []) ≡ (f :: [])
rev-[f::[]]≡[f::[]] {α} {A} f = ⟲ (f :: [])


rev²[f::[]]≡[f::[]] : ∀ {α} {A : ★ α} (f : A) → list-reverse (list-reverse (f :: [])) ≡ (f :: [])
rev²[f::[]]≡[f::[]] {α} {A} f = [rev²[f::[]]≡[f::[]]]
 where
  [rev[f::[]]≡[f::[]] : list-reverse (f :: []) ≡ (f :: [])
  [rev[f::[]]≡[f::[]] = ⟲ (f :: [])

  [rev²[f::[]]≡rev[f::[]]] : list-reverse (list-reverse (f :: [])) ≡ list-reverse (f :: [])
  [rev²[f::[]]≡rev[f::[]]] = [a≡b]→[fa≡fb] list-reverse (list-reverse (f :: [])) (f :: []) [rev[f::[]]≡[f::[]]

  [rev²[f::[]]≡[f::[]]] : list-reverse (list-reverse (f :: [])) ≡ (f :: [])
  [rev²[f::[]]≡[f::[]]] = ≡-⇶ [rev²[f::[]]≡rev[f::[]]] [rev[f::[]]≡[f::[]]
{-
[rev²-[f::r]≡[f::r]]→[rev²-[g::f::r]≡[g::f::r]] : 
 ∀ {α} {A : ★ α} (r : [ A ]) → (f g : A) → 
 list-reverse (list-reverse (f :: r)) ≡ (f :: r) → 
 list-reverse (list-reverse (g :: (f :: r))) ≡ (g :: (f :: r))
[rev²-[f::r]≡[f::r]]→[rev²-[g::f::r]≡[g::f::r]] 
 {α} {A} r f g [rev²-[f::r]≡[f::r]] = [rev²-[g::f::r]≡[g::f::r]]
  where
   
   [rev²-[g::f::r]≡[g::f::r]]
-}
{-
 where
  [rev-[]≡[]] : list-reverse [] ≡ []
  [rev-[]≡[]] = ⟲ []

  [rev²-[]≡rev-[]] : list-reverse (list-reverse []) ≡ list-reverse []
  [rev²-[]≡rev-[]] = [a≡b]→[fa≡fb] list-reverse (list-reverse []) [] [rev-[]≡[]]

  [rev²-[]≡[]] : list-reverse (list-reverse []) ≡ [] 
-}

{-
rev²-l≡l : ∀ {a} {A : ★ α} (l : [ A ]) → list-reverse (list-reverse l) ≡ l
-}












fib-unfib-is-id : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → (a : A) → a ≡ (unfibrate f (fibrate f a))
fib-unfib-is-id {α} {β} {A} {B} f a = ⟲ a


fib-unfib-is-id-strong : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → id ≡ ((unfibrate f) ∘ (fibrate f))
fib-unfib-is-id-strong {α} {β} {A} {B} f = ⟲ (λ a → a)


id-is-injection : ∀ {α} {A : ★ α} → injection (id { α } { A })
id-is-injection {α} {A} = (λ a1 a2 p → p)


id-is-surjection : ∀ {α} {A : ★ α} → surjection (id { α } { A })
id-is-surjection {α} {A} = (λ a → ( a , ⟲ a))


id-is-bijection : ∀ {α} {A : ★ α} → bijection (id { α } { A })
id-is-bijection {α} {A} = ∧-cons id-is-injection id-is-surjection


unfibrate-is-surjection : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → surjection (unfibrate f)
unfibrate-is-surjection {α} {β} {A} {B} f a = ( (f a , (a , ⟲ (f a))) , ⟲ a) 


ex-surjA1-imp-A : ∀ {α} {A : ★ α } {f : A → ⊤} → surjection f -> A
ex-surjA1-imp-A {α} {A} {f} surj = π₁ (surj ●)


ex-surjA1-imp-AB-imp-B : 
 ∀ {α β} {A : ★ α} {B : ★ β} → 
 {a1 : A → ⊤} → surjection a1 → (ab : A → B ) → B
ex-surjA1-imp-AB-imp-B {α} {β} {A} {B} {a1} surj [A→B] = [A→B] ( π₁ (surj ●))

ex-surjA1-imp-AB-imp-BA :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 {a1 : A → ⊤} → surjection a1 →
 (ab : A → B) → B → A
ex-surjA1-imp-AB-imp-BA {α} {β} {A} {B} {[A→⊤]} surj [A→B] b = π₁ (surj ●)


ex-surjA1-imp-AB-imp-FibersAB :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 {a1 : A → ⊤} → surjection a1 → 
 (ab : A → B) -> Fibers ab
ex-surjA1-imp-AB-imp-FibersAB {α} {β} {A} {B} {[A→⊤]} surj [A→B] = (b' , (a' , ⟲ b'))
 where
  a' : A
  a' = π₁ (surj ●)

  b' : B
  b' = [A→B] a'

  
  


ex-surjA1-imp-AB-imp-B-to-FibersAB :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 {a1 : A → ⊤} → surjection a1 → 
 (ab : A → B) → B → Fibers ab
ex-surjA1-imp-AB-imp-B-to-FibersAB {α} {β} {A} {B} {[A→⊤]} surj [A→B] b =
 ex-surjA1-imp-AB-imp-FibersAB surj [A→B]





{-
  Two elements either are or aren't related; not both.
  For any pair of elements (a1,a2), we know that a relation will return either
  true or false; not both, and not neither. We know this because the relation is
  given as a function, and we know how functions behave, but let's go ahead and show
  how to demonstrate that relations actually are well-defined:
-}
relations-are-well-defined : 
  ∀ {α} {A : ★ α} → (_R_ : relation { α } { A }) →
  (x y : A) → (b : 𝔹) → (x R y ≡ b) → (x R y ≡ ! b) → ⊥
relations-are-well-defined {α} {A} R' x y b [xRy≡b] [xRy≡!b] = a≠!a b [b≡!b]
 where
  _R_ : relation {α} {A}
  x R y = R' x y
  infix 2 _R_

  [b≡xRy] : b ≡ x R y
  [b≡xRy] = ≡-↑↓ [xRy≡b]
  
  [b≡!b] : b ≡ ! b
  [b≡!b] = ≡-⇶ [b≡xRy] [xRy≡!b]






{- 
   obviously equivalences & partial orders are preorders, but let's demonstrate it
   anyway
-}
equivalences-are-preorders : 
  ∀ {α} {A : ★ α} → (R : relation { α } { A }) → 
  IsEquivalence R → IsPreorder R
equivalences-are-preorders {n} {A} R eq = ∧-cons R-⟲ R-⇶
 where
  R-⟲ : IsReflexive R
  R-⟲ = ∧-π₁ eq
  
  R-⇶ : IsTransitive R
  R-⇶ = ∧-π₂ (∧-π₂ eq)


partialorders-are-preorders :
  ∀ {α} {A : ★ α} → (R : relation { α } { A }) -> 
  IsPartialOrder R -> IsPreorder R
partialorders-are-preorders {α} {A} R eq = ∧-cons R-⟲ R-⇶
 where
  R-⟲ : IsReflexive R
  R-⟲ = ∧-π₁ eq

  R-⇶ : IsTransitive R
  R-⇶ = ∧-π₂ (∧-π₂ eq)


-- functions are identical to their eta expansions
eta : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → FuncId f (λ x → f x)
eta {α} {β} {A} {B} f a = ⟲ (f a)

eta-strong : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → f ≡ (λ a → f a)
eta-strong {α} {β} {A} {B} f = ⟲ f




-- function composition is associative:
∘-assoc : ∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ δ}
  (f : A → B) → (g : B → C) → (h : C → D) →
  FuncId (h ∘ (g ∘ f)) ((h ∘ g) ∘ f)
∘-assoc {α} {β} {γ} {δ} {A} {B} {C} {D} f g h a = ⟲ (h (g (f a)))

  
∘-assoc-strong : ∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ δ}
  (f : A → B) → (g : B → C) → (h : C → D) →
  h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc-strong {α} {β} {γ} {δ} {A} {B} {C} {D} f g h = ⟲ (λ a → h (g (f a)))

{-
Interactive theorem proving version:

∘-assoc-ITP :
  ∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ δ} →
  (f : A → B) → (g : B → C) → (h : C → D) →
  h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc-ITP {α} {β} {γ} {δ} {A} {B} {C} {D} f g h = refl ?

Then type C-c C-l to load the "?" as a goal
Then type C-c C-s to solve the goal, and we get:

-}



∘-assoc-ITP :
  ∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ δ} →
  (f : A → B) → (g : B → C) → (h : C → D) →
  h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc-ITP {α} {β} {γ} {δ} {A} {B} {C} {D} f g h = ⟲ (h ∘ g ∘ f)


{-
  I could have sworn that when I tried to type in this proof manually that it
  didn't pass type-check, but I haven't been able to reproduce this behavior
  since then. Maybe somebody else can reproduce it?
-}


weak-f-is-g-imp-weak-fib-unfib-f-is-fib-unfib-g :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f g : A → B) → ((unfibrate f) ∘ (fibrate f)) ≡ ((unfibrate g) ∘ (fibrate g))
weak-f-is-g-imp-weak-fib-unfib-f-is-fib-unfib-g {α} {β} {A} {B} f g = 
 ≡-⇶ (≡-↑↓ (fib-unfib-is-id-strong f)) (fib-unfib-is-id-strong g)   

[f1≡f2]→[gf1≡gf2] :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} →
 (f1 f2 : A → B) → f1 ≡ f2 → (g : B → C) →
 g ∘ f1 ≡ g ∘ f2
[f1≡f2]→[gf1≡gf2] {α} {β} {γ} {A} {B} {C} f .f (⟲ .f) g = ⟲ (g ∘ f)


[f1≡f2]→[f1g≡f2g] :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} →
 (f1 f2 : B → C) → f1 ≡ f2 → (g : A → B) →
 f1 ∘ g ≡ f2 ∘ g
[f1≡f2]→[f1g≡f2g] {α} {β} {γ} {A} {B} {C} f .f (⟲ .f) g = ⟲ (f ∘ g)

{-
 
only-False-is-not-implied : 
  {n : Level} {A : Set n} {B : Set} -> 
  Not (A -> B) -> And (Not (Id A False)) (Id B False)
only-False-is-not-implied {n} {A} {B} notAB = 
  record { 
    andFst = ; 
    andSnd = 
  } 

-}

-- Booleans satisfy the Law of the Excluded Middle
𝔹-LEM : (b : 𝔹) → b ≡ 𝕥 ∨ b ≡ 𝕗
𝔹-LEM 𝕥 = ∨-cons1 (⟲ 𝕥)
𝔹-LEM 𝕗 = ∨-cons2 (⟲ 𝕗)


{- 
  Is there anyway to do this without pattern-matching?
-}

-- Boolean logic is consistent (as long as the type theory itself is)
𝔹-consistent : (b : 𝔹) →  (b ≡ 𝕥) ∧ (b ≡ 𝕗) → ⊥
𝔹-consistent b [b≡𝕥]^[b≡𝕗] = ☢
 where
  [b≡𝕥] : b ≡ 𝕥
  [b≡𝕥] = ∧-π₁ [b≡𝕥]^[b≡𝕗]
 
  [b≡𝕗] : b ≡ 𝕗
  [b≡𝕗] = ∧-π₂ [b≡𝕥]^[b≡𝕗]

  [𝕥≡b] : 𝕥 ≡ b
  [𝕥≡b] = ≡-↑↓ [b≡𝕥]
  
  [𝕥≡𝕗] : 𝕥 ≡ 𝕗
  [𝕥≡𝕗] = ≡-⇶ [𝕥≡b] [b≡𝕗]

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]

{-
-- equal functions on equal arguments have equal results:
[f≡g]→[fa≡ga] : 
  ∀ {α β} {A : ★ α} {B : ★ β} →
  (f g : A → B) → (h : f ≡ g) → (a : A) → 
  f a ≡ g a
[f≡g]→[fa≡ga] {α} {β} {A} {B} f .f (⟲ .f) a = ⟲ (f a)

[f≡g]→[fa≡ga]₂ : 
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f g : A → B) → (h : f ≡ g) → (a1 a2 : A) → a1 ≡ a2 → 
 f a1 ≡ g a2
[f≡g]→[fa≡ga]₂ {α} {β} {A} {B} f .f (⟲ .f) a .a (⟲ .a) = ⟲ (f a)
-}

-- equal dep. functions on equal arguments have equal results:
[P≡Q]→[Pa≡Qa] :
  ∀ {α β} {A : ★ α} {B : A → ★ β} →
  (P Q : Π A B) → (hom : P ≡ Q) → (a : A) →
  P a ≡ Q a
[P≡Q]→[Pa≡Qa] {α} {β} {A} {B} f .f (⟲ .f) a = ⟲ (f a)


-- if g after f is the identity, then g is a surjection
[id≡g∘f]→[surj-g] :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → (g : B → A) →
 id ≡ g ∘ f → surjection g
[id≡g∘f]→[surj-g] {α} {β} {A} {B} f g p a = (f a , ≡-↑↓ ([f≡g]→[fa≡ga] id (g ∘ f) p a))


-- if g after f is the identity, then f is an injection
[id≡g∘f]→[inj-f] :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → (g : B → A) →
 id ≡ g ∘ f → injection f
[id≡g∘f]→[inj-f] {α} {β} {A} {B} f g [id≡g∘f] a1 a2 [fa1≡fa2] = [a1≡a2]
 where
  a→[a≡[g∘f]a] : (a : A) → a ≡ (g ∘ f) a
  a→[a≡[g∘f]a] a = [f≡g]→[fa≡ga] id (g ∘ f) [id≡g∘f] a

  [a1≡[g∘f]a1] : a1 ≡ (g ∘ f) a1
  [a1≡[g∘f]a1] = a→[a≡[g∘f]a] a1

  [a2≡[g∘f]a2] : a2 ≡ (g ∘ f) a2
  [a2≡[g∘f]a2] = a→[a≡[g∘f]a] a2

  [[g∘f]a2≡a2] : (g ∘ f) a2 ≡ id a2
  [[g∘f]a2≡a2] = ≡-↑↓ [a2≡[g∘f]a2]

  [[g∘f]a1≡[g∘f]a2] : (g ∘ f) a1 ≡ (g ∘ f) a2
  [[g∘f]a1≡[g∘f]a2] = [a≡b]→[fa≡fb] g (f a1) (f a2) [fa1≡fa2]

  [a1≡[g∘f]a2] : a1 ≡ (g ∘ f) a2
  [a1≡[g∘f]a2] = ≡-⇶ [a1≡[g∘f]a1] [[g∘f]a1≡[g∘f]a2] 

  [a1≡a2] : a1 ≡ a2
  [a1≡a2] = ≡-⇶ [a1≡[g∘f]a2] [[g∘f]a2≡a2]
  


fibrate-is-injection :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → injection (fibrate f)
fibrate-is-injection {α} {β} {A} {B} f = 
 [id≡g∘f]→[inj-f] (fibrate f) (unfibrate f) (fib-unfib-is-id-strong f)


 
unfibrate-is-surjection2 :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → surjection (unfibrate f)
unfibrate-is-surjection2 {α} {β} {A} {B} f =
 [id≡g∘f]→[surj-g] (fibrate f) (unfibrate f) (fib-unfib-is-id-strong f)


-- composition of injections is an injection
inj-⇶ :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} →
 (f : A → B) → injection f →
 (g : B → C) -> injection g →
 injection (g ∘ f)
inj-⇶ {α} {β} {γ} {A} {B} {C} f inj_f g inj_g a1 a2 p = 
 inj_f a1 a2 (inj_g (f a1) (f a2) p)

-- injectivity, surjectivity, and bijectivity are all reflexive:
inj-⟲ :
 ∀ {α} {A : ★ α} → ∃ f ∈ (A → A) , (injection f)
inj-⟲ {a} {A} = (id , id-is-injection)


surj-⟲ :
 ∀ {α} {A : ★ α} → ∃ f ∈ (A -> A) , (surjection f)
surj-⟲ {a} {A} = (id , id-is-surjection)


bij-⟲ :
 ∀ {α} {A : ★ α} → ∃ f ∈ (A -> A) , (bijection f)
bij-⟲ {a} {A} = (id , id-is-bijection)


 
f-of-fiber-f-b-is-b : 
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → (b : B) → (fib : fiber f b) →
 (f (π₁ fib)) ≡ b
f-of-fiber-f-b-is-b {α} {β} {A} {B} f b fib = π₂ fib


-- composition of surjections is a surjection
surj-⇶ :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} →
 (f : A → B) → surjection f →
 (g : B → C) → surjection g →
 surjection (g ∘ f)
surj-⇶ {α} {β} {γ} {A} {B} {C} f surj-f g surj-g c = ( a' , [gfa'≡c])
 where
   b' : B
   b' = π₁ (surj-g c)

   a' : A
   a' = π₁ (surj-f b')

   [fa'≡b'] : f a' ≡ b'
   [fa'≡b'] = π₂ (surj-f b')

   [gfa'≡gb'] : (g ∘ f) a' ≡ g b'
   [gfa'≡gb'] = [a≡b]→[fa≡fb] g (f a') b' [fa'≡b']
  
   [∃b∈B,gb≡c] : ∃ b ∈ B , (g b ≡ c)
   [∃b∈B,gb≡c] = surj-g c

   [gb'≡c] : g b' ≡ c 
   [gb'≡c] = f-of-fiber-f-b-is-b g c (surj-g c)

   [gfa'≡c] : (g ∘ f) a' ≡ c
   [gfa'≡c] = ≡-⇶ [gfa'≡gb'] [gb'≡c]


-- composition of bijections is a bijection
bij-⇶ :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} →
 (f : A → B) → bijection f →
 (g : B → C) → bijection g → 
 bijection (g ∘ f)
bij-⇶ {α} {β} {γ} {A} {B} {C} f bij-f g bij-g = ∧-cons inj-gf surj-gf
 where
  inj-gf : injection (g ∘ f)
  inj-gf = inj-⇶ f (∧-π₁ bij-f) g (∧-π₁ bij-g)

  surj-gf : surjection (g ∘ f)
  surj-gf = surj-⇶ f (∧-π₂ bij-f) g (∧-π₂ bij-g)



-- g is the left-inverse of f 
left-inv : ∀ {α β} {A : ★ α} {B : ★ β} (g : B → A) (f : A → B) → ★ α
left-inv {α} {β} {A} {B} g f = (a : A) → a ≡ (g ∘ f) a

left-inv-strong : ∀ {α β} {A : ★ α} {B : ★ β} (g : B → A) (f : A → B) → ★ α
left-inv-strong {α} {β} {A} {B} g f = id ≡ g ∘ f


right-inv : ∀ {α β} {A : ★ α} {B : ★ β} (g : B → A) (f : A → B) → ★ β
right-inv {α} {β} {A} {B} g f = (b : B) → b ≡ (f ∘ g) b


right-inv-strong : ∀ {α β} {A : ★ α} {B : ★ β} (g : B → A) (f : A → B) → ★ β
right-inv-strong {α} {β} {A} {B} g f = id ≡ (f ∘ g)


left-inv-strong-imp-left-inv-weak : (α β : Level) → ★ (lsuc (α ⊔ β))
left-inv-strong-imp-left-inv-weak α β = 
 {A : ★ α} {B : ★ β} → 
 (g : B → A) → (f : A → B) →
 left-inv-strong g f →
 left-inv g f


prf-left-inv-strong-imp-left-inv-weak : (α β : Level) → left-inv-strong-imp-left-inv-weak α β 
prf-left-inv-strong-imp-left-inv-weak α β {A} {B} g f p a = [f≡g]→[fa≡ga] id (g ∘ f) p a


right-inv-strong-imp-right-inv-weak : (α β : Level) → ★ (lsuc (α ⊔ β))
right-inv-strong-imp-right-inv-weak α β = 
 {A : ★ α} {B : ★ β} → 
 (g : B → A ) → (f : A → B) →
 right-inv-strong g f →
 right-inv g f


prf-right-inv-strong-imp-right-inv-weak : (α β : Level) →  right-inv-strong-imp-right-inv-weak α β
prf-right-inv-strong-imp-right-inv-weak α β {A} {B} g f p b = [f≡g]→[fa≡ga] id (f ∘ g) p b


inv-strong-imp-inv-weak : (α β : Level) →  (left-inv-strong-imp-left-inv-weak α β) ∧ (right-inv-strong-imp-right-inv-weak α β)
inv-strong-imp-inv-weak α β = ∧-cons (prf-left-inv-strong-imp-left-inv-weak α β) (prf-right-inv-strong-imp-right-inv-weak α β)


different-fibers-different-objects :
  ∀ {α β} {A : ★ α} {B : ★ β} → 
  (f : A → B) → (b1 b2 : B) →
  ([b1≠b2] : b1 ≠ b2) →
  (fib1 : fiber f b1) → (fib2 : fiber f b2) →
  π₁ fib1 ≠ π₁ fib2
different-fibers-different-objects {α} {β} {A} {B} f b1 b2 [b1≠b2] fib1 fib2 [a1≡a2] = ☢
 where
  a1 : A
  a1 = π₁ fib1
  
  a2 : A
  a2 = π₁ fib2
 
  [fa1≡b1] : f a1 ≡ b1
  [fa1≡b1] = π₂ fib1
  
  [fa2≡b2] : f a2 ≡ b2
  [fa2≡b2] = π₂ fib2

  [b1≡fa1] : b1 ≡ f a1
  [b1≡fa1] = ≡-↑↓ [fa1≡b1]
 
  [fa1≡fa2] : f a1 ≡ f a2
  [fa1≡fa2] = [a≡b]→[fa≡fb] f a1 a2 [a1≡a2]

  [b1≡fa2] : b1 ≡ f a2
  [b1≡fa2] = ≡-⇶ [b1≡fa1] [fa1≡fa2]

  [b1≡b2] : b1 ≡ b2
  [b1≡b2] = ≡-⇶ [b1≡fa2] [fa2≡b2]

  ☢ : ⊥
  ☢ = [b1≠b2] [b1≡b2]


{-
         ☢
         ^
         |
      [b1≠b2]
         |
      [b1≡b2]
      /      \
     /        \
   [b1≡fa1≡fa2≡b2]
          ^
         f|
       [a1≡a2]
-}


--functions from False to True are injections 
F-T-is-injection : (f : ⊥ → ⊤) → injection f
F-T-is-injection f a1 a2 [fa1≡fa2] = ω a1

--functions from False to True are not surjections
F-T-not-surjection : (f : ⊥ → ⊤) → surjection f → ⊥
F-T-not-surjection f surj = π₁ (surj ●)




--surjection from A to B implies injection from B to A
ex-surj-AB-imp-ex-inj-BA : ∀ {α β} {A : ★ α} {B : ★ β} →
  (f : A → B) → surjection f →
  ∃ g ∈ (B -> A) , (injection g)
ex-surj-AB-imp-ex-inj-BA {α} {β} {A} {B} f surj = (g , inj-g)
  where
   g : B → A
   g = λ b → π₁ (surj b)

   inj-g : injection g
   inj-g b1 b2 [gb1≡gb2] = [b1≡b2]
    where
     gb1 : A
     gb1 = g b1
 
     gb2 : A
     gb2 = g b2
     
     [fgb1≡b1] : f gb1 ≡ b1
     [fgb1≡b1] = π₂ (surj b1)

     [b1≡fgb1] : b1 ≡ f gb1
     [b1≡fgb1] = ≡-↑↓ [fgb1≡b1]
  
     [fgb2≡b2] : f gb2 ≡ b2
     [fgb2≡b2] = π₂ (surj b2)

     [fgb1≡fgb2] : f gb1 ≡ f gb2
     [fgb1≡fgb2] = [a≡b]→[fa≡fb] f gb1 gb2 [gb1≡gb2]
    
     [b1≡fgb2] : b1 ≡ f gb2
     [b1≡fgb2] = ≡-⇶ [b1≡fgb1] [fgb1≡fgb2]

     [b1≡b2] : b1 ≡ b2
     [b1≡b2] = ≡-⇶ [b1≡fgb2] [fgb2≡b2]



--injection from A to B doesn't imply surjection from B to A
ex-inj-AB-nimp-ex-surj-BA :
  (∀ {α β} {A : ★ α} {B : ★ β} →
  (f : A → B) → injection f →
  ∃ g ∈ (B -> A) , (surjection g)) → ⊥
ex-inj-AB-nimp-ex-surj-BA hyp = ☢
 where
  [∃g∈[⊤→⊥],surj-g] : ∃ g ∈ (⊤ → ⊥) , (surjection g)
  [∃g∈[⊤→⊥],surj-g] = hyp ⊥→⊤ (F-T-is-injection ⊥→⊤)

  [⊤→⊥] : ⊤ → ⊥
  [⊤→⊥] = π₁ [∃g∈[⊤→⊥],surj-g]
  
  ☢ : ⊥
  ☢ = [⊤→⊥] ●



--not exists surjection A to B doesn't imply exists injection A to B
nex-surj-AB-nimp-ex-inj-AB : 
  (∀ {α β} {A : ★ α} {B : ★ β} →
  ((f : A → B) → surjection f → ⊥) → 
  ∃ g ∈ (A -> B) , (injection g)) → ⊥
nex-surj-AB-nimp-ex-inj-AB hyp = ☢ 
 where
  [∃g∈[⊤→⊥],inj-g] : ∃ g ∈ (⊤ → ⊥) , (injection g)
  [∃g∈[⊤→⊥],inj-g] = hyp { lzero } { lzero } { ⊤ } { ⊥ } (λ [⊤→⊥] surj → [⊤→⊥] ●)

  [⊤→⊥] : ⊤ → ⊥
  [⊤→⊥] = π₁ [∃g∈[⊤→⊥],inj-g]
  
  ☢ : ⊥
  ☢ = [⊤→⊥] ●


--not exists injection A to B doesn't imply exists surjection A to B
nex-inj-AB-nimp-ex-surj-AB :
  (∀ {α β} {A : ★ α} {B : ★ β} →
   ((f : A → B) → injection f → ⊥) →
   ∃ g ∈ (A → B) , (surjection g)) → ⊥
nex-inj-AB-nimp-ex-surj-AB hyp = ☢
 where
  [∃g∈[⊤→⊥],surj-g] : ∃ g ∈ (⊤ → ⊥) , (surjection g)
  [∃g∈[⊤→⊥],surj-g] = hyp { lzero } { lzero } { ⊤ } { ⊥ } (λ [⊤→⊥] inj → [⊤→⊥] ●)

  [⊤→⊥] : ⊤ → ⊥
  [⊤→⊥] = π₁ [∃g∈[⊤→⊥],surj-g]

  ☢ : ⊥
  ☢ = [⊤→⊥] ●

{-

--exists surjection B to 1 and not-exists injection A to B implies exists surjection A to B
--intuitively: if B is not empty, and A doesn't fit in B, then A covers B with a surjection
ex-surj-B1-nex-inj-AB-imp-ex-surj-AB :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : B -> True) -> surjection f ->
  ((g : A -> B) -> injection g -> False) ->
  Sigma (A -> B) surjection
ex-surj-B1-nex-inj-AB-imp-ex-surj-AB {m} {n} {A} {B} f surj_f noinjAB =

-}


surjection-fiber-reverse :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → surjection f → 
 (b : B) → Fibers f
surjection-fiber-reverse {α} {β} {A} {B} f surj-f b = (b , surj-f b)
 


{-
--exists surjection A to 1 and exists injection A to B implies exists surjection B to A
--intuitively: if A is not empty, and A fits in B, then B covers A with a surjection

ex-surj-A1-ex-inj-AB-imp-ex-surj-BA :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> True) -> surjection f ->
  (g : A -> B) -> injection g ->
  Sigma (B -> A) surjection
ex-surj-A1-ex-inj-AB-imp-ex-surj-BA {m} {n} {A} {B} f surj_f g inj_g = 
-}

-- reverse the fibers of the injection
-- map every other point in B to an arbitrary object in A
-- but how to tell Agda to do this?



{-
--exists surjection B to 1 and not-exists surjection A to B implies exists injection A to B
--intuitively: if B is not empty, and A doesn't cover B, then A fits in B
ex-surj-B1-nex-surj-AB-imp-ex-inj-AB :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : B -> True) -> surjection f ->
  ((g : A -> B) -> surjection g -> False) ->
  Sigma (A -> B) injection
ex-surj-B1-nex-surj-AB-imp-ex-inj-AB {m} {n} {A} {B} f surj_f nosurjAB =

-}



{-
--injection A to B, injection B to A implies bijection A to B
inj-antisym :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> B) -> injection f ->
  (g : B -> A) -> injection g ->
  bijection f
inj-antisym {m} {n} {A} {B} f inj-f g inj-g =
-}

{-
inj-antisym2 :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection f ->
 (g : B -> A) -> injection g -> 
 bijective A B
inj-antisym2 {m} {n} {A} {B} f inj-f g inj-g =
 record {
  proj1 = 
 }
-}


-- fibers of injections are contractible
fiber-inj-b-is-unique :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → injection f → 
 (b : B) → (fib1 : fiber f b) → (fib2 : fiber f b) →
 (π₁ fib1) ≡ (π₁ fib2)
fiber-inj-b-is-unique {α} {β} {A} {B} f inj-f b fib1 fib2 = [a1≡a2]
 where
  a1 : A
  a1 = π₁ fib1
 
  a2 : A
  a2 = π₁ fib2

  [fa1≡b] : f a1 ≡ b
  [fa1≡b] = π₂ fib1

  [fa2≡b] : f a2 ≡ b
  [fa2≡b] = π₂ fib2

  [b≡fa2] : b ≡ f a2
  [b≡fa2] = ≡-↑↓ [fa2≡b]

  [fa1≡fa2] : f a1 ≡ f a2
  [fa1≡fa2] = ≡-⇶ [fa1≡b] [b≡fa2]

  [a1≡a2] : a1 ≡ a2
  [a1≡a2] = inj-f a1 a2 [fa1≡fa2]
 

surj-inj-imp-ex-a1-a2-where-surj-a1-eq-inj-a2 :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → surjection f →
 (g : A → B) → injection g →
 (b : B) → ∃ a1 ∈ A , (∃ a2 ∈ A , (g a1 ≡ f a2)) 
surj-inj-imp-ex-a1-a2-where-surj-a1-eq-inj-a2 {α} {β} {A} {B} f surj-f g inj-g b = (a1 , (a2 , [ga1≡fa2]))
 where
  a1 : A
  a1 = π₁ (surj-f b)

  a2 : A
  a2 = π₁ (surj-f (g a1))

  [fa2≡ga1] : f a2 ≡ g a1
  [fa2≡ga1] = π₂ (surj-f (g a1))

  [ga1≡fa2] = ≡-↑↓ [fa2≡ga1]


func-matching-surj-is-surj :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → surjection f →
 (g : A → B) → ((a : A) → (g a) ≡ (f a)) →
 (b : B) → ∃ a ∈ A , (g a ≡ b)
func-matching-surj-is-surj {m} {n} {A} {B} f surj-f g a→[ga≡fa] b = (a , [ga≡b])
 where
  a : A
  a = π₁ (surj-f b)
  
  [ga≡fa] : g a ≡ f a
  [ga≡fa] = a→[ga≡fa] a

  [fa≡b] : f a ≡ b
  [fa≡b] = f-of-fiber-f-b-is-b f b (surj-f b)

  [ga≡b] : g a ≡ b
  [ga≡b] = ≡-⇶ [ga≡fa] [fa≡b] 
  

func-matching-inj-is-inj :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → injection f →
 (g : A → B) → ((a : A) → g a ≡ f a) →
 (a1 a2 : A) → (g a1 ≡ g a2) -> (a1 ≡ a2)
func-matching-inj-is-inj {m} {n} {A} {B} f inj-f g a→[ga≡fa] a1 a2 [ga1≡ga2] = [a1≡a2]
 where
  [ga1≡fa1] : g a1 ≡ f a1
  [ga1≡fa1] = a→[ga≡fa] a1
  
  [fa1≡ga1] : f a1 ≡ g a1
  [fa1≡ga1] = ≡-↑↓ [ga1≡fa1]

  [ga2≡fa2] : g a2 ≡ f a2
  [ga2≡fa2] = a→[ga≡fa] a2

  [ga1≡fa2] : g a1 ≡ f a2
  [ga1≡fa2] = ≡-⇶ [ga1≡ga2] [ga2≡fa2]

  [fa1≡fa2] : f a1 ≡ f a2
  [fa1≡fa2] = ≡-⇶ [fa1≡ga1] [ga1≡fa2]

  [a1≡a2] : a1 ≡ a2
  [a1≡a2] = inj-f a1 a2 [fa1≡fa2]
  



{-
surjective-imp-inj-is-surj :
 ({m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f -> 
 (g : A -> B) -> injection g -> 
 (b : B) -> Sigma A \{a -> Id (g a) b}) -> False
surjective-imp-inj-is-surj {m} {n} {A} {B} hyp = 
-} 

--counterexample : 
-- f(n) = n is a surjection Z -> Z
-- f(n) = 2n is an injection Z -> Z
-- but the injection is not a surjection
-- proof: there is no n:Z such that 4n = 2


bijection-invertible :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → bijection f →
 ∃ g ∈ (B → A) , (left-inv g f)
bijection-invertible {α} {β} {A} {B} f bij-f = (g , g-left-inv-f)
 where
  inj-f : injection f
  inj-f = ∧-π₁ bij-f

  surj-f : surjection f
  surj-f = ∧-π₂ bij-f

  g : B → A
  g b = a
   where
    Fib-b : ∃ b ∈ B , (∃ a ∈ A , (f a ≡ b))
    Fib-b = surjection-fiber-reverse f surj-f b
   
    fib-b : ∃ a ∈ A , (f a ≡ b)
    fib-b = π₂ Fib-b

    a : A
    a = π₁ fib-b

  g-left-inv-f : left-inv g f
  g-left-inv-f a = inj-f a a' [fa≡fa']
   where
    Fib-b : ∃ b ∈ B , (∃ a' ∈ A , (f a' ≡ b))
    Fib-b = surjection-fiber-reverse f surj-f (f a)
 
    fib-b : ∃ a' ∈ A , (f a' ≡ f a)
    fib-b = π₂ Fib-b

    a' = π₁ fib-b

    [fa'≡fa] : f a' ≡ f a
    [fa'≡fa] = f-of-fiber-f-b-is-b f (f a) fib-b

    [fa≡fa'] : f a ≡ f a'
    [fa≡fa'] = ≡-↑↓ [fa'≡fa]


{-
bijectivity-symmetric :
 {m n : Level} {A : Set m} {B : Set n} ->
 bijective A B -> bijective B A
bijectivity-symmetric {m} {n} False False bijAB = record {andFst = id; andSnd = id}
bijectivity-symmetric {m} {n} {A} {B} bijAB =
 record {
  andFst =  ex-surj-AB-imp-ex-inj-BA (proj1 (andFst bijAB)) (proj2 (andFst bijAB));
  andSnd =  ;
 }
-}



{-
injective-imp-surj-is-inj-is-false :
 ({m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection f ->
 (g : A -> B) -> surjection g ->
 (a1 a2 : A) -> Id (g a1) (g a2) -> Id a1 a2) -> False
injective-imp-surj-is-inj hyp = 
-}


--counterexample :
--There are bijections between Z and 2Z:
--f(n) = 2n 
--f(n) = 2*ceiling(n/2) is a surjection Z -> 2Z, but not an injection



--surjection A to B, surjection B to A implies bijection A to B
{-
surj-antisym-is-false :
 ({m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f ->
 (g : B -> A) -> surjection g ->
 bijection f) -> False
surj-antisym2 hyp =
-}




{-
surj-antisym2 :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> B) -> surjection f ->
  (g : B -> A) -> surjection g ->
  Sigma (A -> B) \{bij -> bijection bij}
surj-antisym2 {m} {n} {A} {B} f surj-f g surj-g =
 record {
  proj1 = ?
  proj2 = record { 
   andFst = injection proj1
   andSnd = surjection proj1
  }
 }
-}

--Method 1:
--ex-surj-AB-imp-ex-inj-BA will tell us that an injection A -> B does exist
--surjective-imp-inj-is-surj would then tell us that this injection is also a surjection,
--completing the proof.

--Method 2:
--ex-surj-AB-imp-ex-inj-BA will tell us that an injection A -> B does exist
--injective-imp-surj-is-inj would then tell us that the surjection f is also an injection,
--completing the proof.
--This also proves "surj-antisym" and not just "surj-antisym2"




-- surjectivity is antisymmetric
surj-antisym3 :
 ∀ {α β} {A : ★ α} {B : ★ β} →
 (f : A → B) → surjection f →
 (g : B → A) → surjection g →
 bijective A B
surj-antisym3 {α} {β} {A} {B} f surj-f g surj-g = ∧-cons (injAB) (surjAB)
 where
  [∃i∈[A→B],inj-i] : ∃ i ∈ (A → B) , (injection i)
  [∃i∈[A→B],inj-i] = ex-surj-AB-imp-ex-inj-BA g surj-g

  

  injAB : injective A B
  injAB = (π₁ [∃i∈[A→B],inj-i] , π₂ [∃i∈[A→B],inj-i])

  surjAB : surjective A B
  surjAB = (f , surj-f)




[f1≡f2]→[g∘f1≡g∘f2] :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} (f1 f2 : A → B) → f1 ≡ f2 → (g : B → C) → (g ∘ f1 ≡ g ∘ f2)
[f1≡f2]→[g∘f1≡g∘f2] {α} {β} {γ} {A} {B} {C} f1 f2 [f1≡f2] g = [g∘f1≡g∘f2]
 where
  g∘ : (A → B) → (A → C)
  g∘ f = g ∘ f 

  [g∘f1≡g∘f2] : g ∘ f1 ≡ g ∘ f2
  [g∘f1≡g∘f2] = [f≡g]→[fa≡ga]₂ g∘ g∘ (⟲ g∘) f1 f2 [f1≡f2]




[f1≡f2]→[∘f1≡∘f2] : 
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ}
 (f1 f2 : A → B) → f1 ≡ f2 → ∘' { α } { β } { γ } { A } { B } { C } f1 ≡ ∘' { α } { β } { γ } { A } { B } { C } f2
[f1≡f2]→[∘f1≡∘f2] {α} {β} {γ} {A} {B} {C} f1 f2 [f1≡f2] = [∘f1≡∘f2]
 where
  [∘f1≡∘f2] : ∘' f1 ≡ ∘' f2
  [∘f1≡∘f2] = [f≡g]→[fa≡ga]₂ ∘' ∘' (⟲ ∘') f1 f2 [f1≡f2]





[f1≡f2]→[g∘f1≡g∘f2]₂ :
 ∀  {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} (f1 f2 : A → B) → f1 ≡ f2 → (g : B → C) → (g ∘ f1 ≡ g ∘ f2)
[f1≡f2]→[g∘f1≡g∘f2]₂ {α} {β} {γ} {A} {B} {C} f1 f2 [f1≡f2] g = [g∘f1≡g∘f2]
 where
  ∘f1 : (B → C) → A → C
  ∘f1 = ∘' f1

  ∘f2 : (B → C) → A → C
  ∘f2 = ∘' f2

  [g∘f1≡g∘f2] : g ∘ f1 ≡ g ∘ f2
  [g∘f1≡g∘f2] = [f≡g]→[fa≡ga] ∘f1 ∘f2 [∘f1≡∘f2] g
   where
    [∘f1≡∘f2] : ∘f1 ≡ ∘f2
    [∘f1≡∘f2] = [f1≡f2]→[∘f1≡∘f2] f1 f2 [f1≡f2]

[g1≡g2]→[g1∘≡g2∘] :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} 
 (g1 g2 : B → C) → g1 ≡ g2 → 
 _∘_ { α } { β } { γ } { A } { B } { C } g1 ≡ _∘_ { α } { β } { γ } { A } { B } { C } g2
[g1≡g2]→[g1∘≡g2∘] {α} {β} {γ} {A} {B} {C} g1 g2 [g1≡g2] = [g1∘≡g2∘]
 where
  [g1∘≡g2∘] : _∘_ { α } { β } { γ } { A } { B } { C } g1 ≡ _∘_ { α } { β } { γ } { A } { B } { C } g2
  [g1∘≡g2∘] = [f≡g]→[fa≡ga]₂ _∘_ _∘_ (⟲ _∘_) g1 g2 [g1≡g2]
  

[g1≡g2]→[g1∘f≡g2∘f] :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ}
 (g1 g2 : B → C) → g1 ≡ g2 → (f : A → B) →
 g1 ∘ f ≡ g2 ∘ f
[g1≡g2]→[g1∘f≡g2∘f] {α} {β} {γ} {A} {B} {C} g1 g2 [g1≡g2] f = [g1∘f≡g2∘f]
 where
  g1∘ : (A → B) → A → C
  g1∘ = _∘_ g1

  g2∘ : (A → B) → A → C
  g2∘ = _∘_ g2

  [g1∘f≡g2∘f] : g1 ∘ f ≡ g2 ∘ f
  [g1∘f≡g2∘f] = [f≡g]→[fa≡ga] g1∘ g2∘ [g1∘≡g2∘] f
   where
    [g1∘≡g2∘] : _∘_ g1 ≡ _∘_ g2
    [g1∘≡g2∘] = [g1≡g2]→[g1∘≡g2∘] g1 g2 [g1≡g2]
  


unop-Δ :
 ∀ {α β} {A : ★ α} {B : ★ β}
 ([A≅B] : true-iso A B) → (f : A → A) →
 ∃ g ∈ (B → B) , 
  ((π₁ (π₂ [A≅B])) ∘ g ∘ (π₁ [A≅B]) ≡ f)
unop-Δ {α} {β} {A} {B} (F , (G , ∧-cons [G∘F≡id] [F∘G≡id])) f = ((F ∘ (f ∘ G)) , [G∘g∘F≡f])
 where
  
  g : B → B
  g = F ∘ f ∘ G 

  G∘F∘ : (A → A) → A → A
  G∘F∘ f a = (G ∘ F ∘ f) a 
 
  _∘G∘F : (A → A) → A → A
  _∘G∘F f a = (f ∘ G ∘ F) a
  
  id∘ : (A → A) → A → A
  id∘ f = f

  _∘id : (A → A) → A → A
  _∘id f = f

  [G∘F∘≡id∘] : G∘F∘ ≡ id∘ 
  [G∘F∘≡id∘] = [g1≡g2]→[g1∘≡g2∘] (G ∘ F) id [G∘F≡id]

  [∘G∘F≡∘id] : _∘G∘F ≡ _∘id
  [∘G∘F≡∘id] = [f1≡f2]→[∘f1≡∘f2] (G ∘ F) id [G∘F≡id]

  [G∘F∘f∘G∘F≡f∘G∘F] : (G ∘ F ∘ f ∘ G ∘ F) ≡ f ∘ G ∘ F
  [G∘F∘f∘G∘F≡f∘G∘F] = [f≡g]→[fa≡ga] G∘F∘ id∘ [G∘F∘≡id∘] (f ∘ G ∘ F)
  
  [f∘G∘F≡f] : f ∘ G ∘ F ≡ f
  [f∘G∘F≡f] = [f≡g]→[fa≡ga] _∘G∘F _∘id [∘G∘F≡∘id] f 

  [G∘g∘F≡f] : (G ∘ F ∘ f ∘ G ∘ F) ≡ f
  [G∘g∘F≡f] = ≡-⇶ [G∘F∘f∘G∘F≡f∘G∘F] [f∘G∘F≡f]

{-
binop-Δ : 
 ∀ {α β} {A : ★ α} {B : ★ β} 
 ([A≅B] : true-iso A B) → (+ : A → A → A) → 
 ∃ * ∈ (B → B → B) , 
  ((a1 a2 : A) → ((π₁ (π₂ [A≅B])) (* ((π₁ [A≅B]) a1) ((π₁ [A≅B]) a2)) ≡ (+ a1 a2)))  
binop-Δ {α} {β} {A} {B} (f , (g , fg-inv)) +' = (_⊗_ , commutes)
 where
  _⊕_ : A → A → A
  x ⊕ y = +' x y
  infix 2 _⊕_

  [g∘f≡id] : g ∘ f ≡ id
  [g∘f≡id] = ∧-π₁ fg-inv

  [f∘g≡id] : f ∘ g ≡ id
  [f∘g≡id] = ∧-π₂ fg-inv

  _⊗_ : B → B → B
  b1 ⊗ b2 = f ((g b1) ⊕ (g b2))
  infix 2 _⊗_
  
  commutes : (a1 a2 : A) → g ((f a1) ⊗ (f a2)) ≡ a1 ⊕ a2
--  commutes : (a1 a2 : A) → g (f ((g (f a1)) ⊕ (g (f a2)))) ≡ a1 + a2
  commutes a1 a2 = [g[fa1*fa2]≡a1+a2]
   where 
    [gf[gfa1+gfa2]] : A
    [gf[gfa1+gfa2]] = g (f ((g (f a1)) ⊕ (g (f a2))))

    [gf[gfa1+gfa2]≡g[fa1*fa2]] : g (f ((g (f a1)) ⊕ (g (f a2)))) ≡ g ((f a1) ⊗ (f a2)) 
    [gf[gfa1+gfa2]≡g[fa1*fa2]] = ⟲ (g (f ((g (f a1)) ⊕ (g (f a2)))))

    [g[fa1*fa2]≡gf[gfa1+gfa2]] : g ((f a1) ⊗ (f a2)) ≡ g (f ((g (f a1)) ⊕ (g (f a2))))
    [g[fa1*fa2]≡gf[gfa1+gfa2]] = ≡-↑↓ [gf[gfa1+gfa2]≡g[fa1*fa2]]

    [gf[gfa1+gfa2]≡gfa1+gfa2] : g (f ((g (f a1)) ⊕ (g (f a2)))) ≡ (g (f a1)) ⊕ (g (f a2))
    [gf[gfa1+gfa2]≡gfa1+gfa2] = [f≡g]→[fa≡ga] (g ∘ f) id [g∘f≡id] ((g (f a1)) ⊕ (g (f a2))) 
 
    [g[fa1*fa2]≡gfa1+gfa2] : g ((f a1) ⊗ (f a2)) ≡ (g (f a1)) ⊕ (g (f a2))
    [g[fa1*fa2]≡gfa1+gfa2] = ≡-⇶ [g[fa1*fa2]≡gf[gfa1+gfa2]] [gf[gfa1+gfa2]≡gfa1+gfa2]

    [[gfa1]≡a1] : g (f a1) ≡ a1
    [[gfa1]≡a1] = [f≡g]→[fa≡ga] (g ∘ f) id [g∘f≡id] a1   

    [[gfa2]≡a2] : g (f a2) ≡ a2
    [[gfa2]≡a2] = [f≡g]→[fa≡ga] (g ∘ f) id [g∘f≡id] a2

    [gfa1+_≡a1+_] : (λ a2' → (g (f a1)) ⊕ a2') ≡ (λ a2' →  a1 ⊕ a2')
    [gfa1+_≡a1+_] = [f≡g]→[fa≡ga]₂ new new (⟲ new) (g (f a1)) a1 [[gfa1]≡a1]
     where
      new : A → (A → A)
      new a1' a2' = a1' ⊕ a2'
 
    [gfa1+gfa2≡a1+a2] : (g (f a1)) ⊕ (g (f a2)) ≡ a1 ⊕ a2
    [gfa1+gfa2≡a1+a2] = [f≡g]→[fa≡ga]₂ new1 new2 [gfa1+_≡a1+_] (g (f a2)) a2 [[gfa2]≡a2]
     where
       new1 : A → A
       new1 a2' = (g (f a1)) ⊕ a2'
     
       new2 : A → A
       new2 a2' = a1 ⊕ a2'
 
        

    [g[fa1*fa2]≡a1+a2] : g ((f a1) ⊗ (f a2)) ≡ a1 ⊕ a2
    [g[fa1*fa2]≡a1+a2] = ≡-⇶ [g[fa1*fa2]≡gfa1+gfa2] [gfa1+gfa2≡a1+a2]  

record Square {α β γ δ} (tl : ★ α) (tr : ★ β) (bl : ★ γ) (br : ★ δ) : ★ ((α ⊔ β) ⊔ (γ ⊔ δ)) where
 field
  top : tl → tr
  bottom : bl → br
  left : tl → bl
  right : tr → br
open Square public

commutes-strong : 
 ∀ {α β γ δ} {tl : ★ α} {tr : ★ β} {bl : ★ γ} {br : ★ δ} →
 (Square tl tr bl br) → ★ (α ⊔ δ)
commutes-strong □ = (bottom □) ∘ (left □) ≡ (right □) ∘ (top □)

 
commutes-weak :
 ∀ {α β γ δ} {tl : ★ α} {tr : ★ β} {bl : ★ γ} {br : ★ δ} →
 Square tl tr bl br → ★ (α ⊔ δ)
commutes-weak {a} {β} {γ} {δ} {tl} {bl} {tr} {br} □ = (a : tl) → ((bottom □) ∘ (left □)) a ≡ ((right □) ∘ (top □)) a


commutes-strong→commutes-weak : 
 ∀ {α β γ δ} {tl : ★ α} {tr : ★ β} {bl : ★ γ} {br : ★ δ}
 (□ : Square tl tr bl br) → commutes-strong □ → commutes-weak □
commutes-strong→commutes-weak □  □-strong a = [f≡g]→[fa≡ga] ((bottom □) ∘ (left □)) ((right □) ∘ (top □)) □-strong a


func-Δ : ∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ δ}
 ([A≅C] : true-iso A C) → ([B≅D] : true-iso B D) →  
 (f : A → B) →
 ∃ g ∈ (C → D) , (((π₁ (π₂ [B≅D])) ∘ g ∘ (π₁ [A≅C])) ≡ f)
func-Δ 
 {α} {β} {γ} {δ} {A} {B} {C} {D} 
 ([A→C] , ([C→A] , (∧-cons [[C→A]∘[A→C]≡id] [[A→C]∘[C→A]≡id])))
 ([B→D] , ([D→B] , (∧-cons [[D→B]∘[B→D]≡id] [[B→D]∘[D→B]≡id])))
 [A→B] 
  = ([C→D] , [[D→B]∘[C→D]∘[A→C]≡[A→B]])
  where
   [C→D] : C → D
   [C→D] = [B→D] ∘ [A→B] ∘ [C→A] 
 
   [[D→B]∘[C→D]∘[A→C]≡[A→B]∘[C→A]∘[A→C]] : ([D→B] ∘ [C→D] ∘ [A→C]) ≡ ([A→B] ∘ [C→A] ∘ [A→C])
   [[D→B]∘[C→D]∘[A→C]≡[A→B]∘[C→A]∘[A→C]] = [g1≡g2]→[g1∘f≡g2∘f] ([D→B] ∘ [B→D]) id [[D→B]∘[B→D]≡id] ([A→B] ∘ [C→A] ∘ [A→C])

   [[A→B]∘[C→A]∘[A→C]≡[A→B]] : ([A→B] ∘ [C→A] ∘ [A→C]) ≡ [A→B]
   [[A→B]∘[C→A]∘[A→C]≡[A→B]] = [f1≡f2]→[g∘f1≡g∘f2] ([C→A] ∘ [A→C]) id [[C→A]∘[A→C]≡id] [A→B]
  
   [[D→B]∘[C→D]∘[A→C]≡[A→B]] : [D→B] ∘ [C→D] ∘ [A→C] ≡ [A→B]
   [[D→B]∘[C→D]∘[A→C]≡[A→B]] = ≡-⇶ [[D→B]∘[C→D]∘[A→C]≡[A→B]∘[C→A]∘[A→C]] [[A→B]∘[C→A]∘[A→C]≡[A→B]]
-}
{-
[func-Δ]→[binop-Δ] : 
 ∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ d} →
 func-Δ
-}

{-
func-iso :

-}


{-
SemiGroup-Δ : 
 ∀ {α β} (A : ★ α) (B : ★ β) ([A≅B] : true-iso A B)
 ([a→a] : A → A) →
 ∃ [b→b] : (B → B) , 
  (
  
-}

{-
OpTypeCreate : ∀ {α} (A : ★ α) (n : ℕ) → ★ α
OpTypeCreate A 𝕫 = ⊥-level
OpTypeCreate A (𝕤 𝕫) = A
OpTypeCreate A (𝕤 n) = A → OpTypeCreate A n 

record Op {α} (A : ★ α) : ★ α where
 field
  arity : ℕ
  op : OpTypeCreate A arity



Op-Δ : ∀ {α β} (A : ★ α) (B : ★ β) ([A≅B] : true-iso A B) (n : ℕ) (op-A : OpTypeCreate A n) →
 ∃ op-B : OpTypeCreate B n , (
-}
