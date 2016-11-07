module unicode where


open import Agda.Primitive public

--http://www.cse.chalmers.se/~nad/listings/lib/Agda.Primitive.html
{-

-- The Agda primitives (preloaded).

module Agda.Primitive where

------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

infixl 6 _⊔_

postulate
  Level : Set
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# COMPILED_TYPE Level ()      #-}
{-# COMPILED lzero ()           #-}
{-# COMPILED lsuc  (\_ -> ())   #-}
{-# COMPILED _⊔_   (\_ _ -> ()) #-}

{-# BUILTIN LEVEL     Level  #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX  _⊔_    #-}


-}

--https://github.com/agda/agda/blob/master/src/data/lib/prim/Agda/Primitive.agda
{-
-- The Agda primitives (preloaded).

{-# OPTIONS --without-K #-}

module Agda.Primitive where

------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

infixl 6 _⊔_

-- Level is the first thing we need to define.
-- The other postulates can only be checked if built-in Level is known.

postulate
  Level : Set

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# COMPILED_TYPE Level () #-}
{-# BUILTIN LEVEL Level    #-}

postulate
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

-}


--In Agda 2.5 you have to import Agda.Primitive in order to access the universe levels, you can't
--bind the LEVEL builtins to your own postulated Level types anymore, which was how you set up
--Levels in Agda 2.3

{-



How to set up my character scheme:

Wherever it says "set", then you need to add the Unicode character and the 
key-sequence to the list in agda-input-user-translations. This allows you
to use those special characters by typing the key-sequence.

Wherever it says "override attached list", this means that agda-input-translations
actually defines a list of characters attached to the key-sequence, rather than
a single character, so you can type out the key-sequence and then scroll through
the list using the left/right/up/down arrows on the keyboard to choose a specific
character. However, this can be annoying when you're editing code, because you might
type the key-sequence for a special character and then try to move forward in the
text using the right-arrow, but you just end up moving through the character selector
and changing your character instead. So if you find that annoying as well then
you can disable these lists by assigning them to another key-sequence (or just
deleting them if you don't think you'd ever use those particular characters).

You can access these lists via:

M-x customize-variable agda-input-user-translations
M-x customize-variable agda-input-translations 

The following key-sequences also have definitions outside of agda-input-translations and these
would have to be disabled in order to prevent them having a character-selector, but I still haven't
found where they are defined: 
 \b
 \L
 \l
 \o
 \P
 \S 



Char  Key-Sequence   -- Instructions
================================================================
ℓ      \L             -- set ; override list Ł
ℓ₀     \l0            -- set
ℓ₁     \l1            -- set
⊔      \max           -- set


α      \a             -- set
β      \b             -- set ; override list → delete both ♭ and ̱
γ      \g             -- set
δ      \d             -- set ; override list → downarrow and .. ?

★      \set           -- set
★₀     \set0          -- set
★₁     \set1          -- set


⊤      \T             -- set ; override list → Triangle 
⊥      \F             -- set
¬      \not
⊹  ∨   \+      \or
×  ∧   \x      \and
→      \r \to          -- set r ; override list → rightarrow
Π  ∀   \P      \A      -- set P ( override ¶ ); set A
Σ  ∃   \S      \E      -- set S ( override § ); set E
∄      \exn 


λ      \l              -- set ; override list    → leftarrow
                       --       override ł 
Δ      \D              -- set
Γ      \G              -- set

∘      \o              --override ø 

For the common sets in math: the naturals, reals, complex, rationals,
integers, and booleans, I'm using the blackboard bold characters used in
standard mathematical notation, with the addition of 𝔹 for Bool.

𝔹     \B     \bb       -- set
ℂ     \C     \bc       -- set ; override list → oldC 
ℕ     \N     \bn       -- set
ℚ     \Q     \bq       -- set 
ℝ     \R     \br       -- set 
ℤ     \Z     \bz       -- set  

For the constructors of the common types I'm using special Unicode 
characters to get them down to one symbol without having to overlap
with any ASCII character that might be used as a variable in an 
expression.

⊤:
●            \ci            

agda-mode renders this green so I think of it like a "green light on"
green lights on typically indicate something being "true" in some kind
of way

𝔹:
𝕥 = true     \t             -- set ; override list → triangle  
𝕗 = false    \f             -- set


ℕ:
𝕫 = zero    \z             -- set
𝕤 = suc     \s             -- set

⊥:


I'm also using some Unicode symbols for the common ≡ and ≠ . 

≡     \eq            -- set ; override ; use \== temporarily 
≢     \neq           -- set ; override
≠     \ne

And the refl constructor:

⟲  = refl       \refl

You can think of this as visually being a path from the object back
to itself. Could maybe set a syntax macro so that "a⟲" evaluates to "⟲ a"
to further the visual representation of the reflexor.

⊥:
ω      \w            -- set
☢     \nuke         -- set

False of course has no proofs, but it does have an elim, which we'll represent by ω, and
you can assume a proof of False or derive a proof of False under assumptions, and we can
use the ☢ symbol for that, which I like because it's sort of like taking the proof of False
and nuking the system with it


↔ is a bit too small for easy reading, so I'm using ⇆ for bi-implication instead:
⇆     \bi            -- set


Standard notation for the inverse of an object:
⁻¹    \inv           -- set


We can't make syntax declarations that use the ":" character, so we can
use the ∈ character instead which is more common in standard mathematical
notation anyway:

∈     \in

Mechanically verified mathematics requires a lot of proof
information to be transfered around from other results in order to
construct a proof from them, using specific operations of construction so
that a machine can verify the proof structures. This is typically the 
informational content of the natural language paragraphs that surround
the symbolic formulas in literature.

However, if you try to use words as identifiers for the objects/functions you 
use in proof construction, then your proofs become cluttered and unreadable 
just like predicate logic propositions become cluttered and unreadable when 
you replace the logical constants and predicates with natural language words. 
Unfortunately, people haven't spent hundreds of years developing a clean,
clear and concise notation for this proof-construction information like they
did for logical predicates and equations. So, I'm experimenting with some
ways to systematically symbolize concepts that are commonly employed in 
proof-constructions:

↑↓  symmetric   \sym           -- set
⇶   transitive  \trans          -- set


=====================================================
Operator precedence

Both propositions and proofs become quickly cluttered with expressions,
so it's best to be able to drop as many parentheses as possible in order
to declutter your expressions, but removing too many parentheses can
introduce ambiguity. When this happens you can remove the ambiguity by
introducing an order of operations, i.e. assigning a binding precedence
to your operations. I have chosen this operator precedence scheme in order
to conform as closely as possible to standard mathematical notation:

∧    0
∨    0
≡    1
∘    2

=====================================================
Language notes:

1) Should use := for definitional equality in function definitions
   to keep = available for propositional equality.

2) "(a : A) →" should be interchangeable with "∀ a : A, "
   * note: dropping parentheses, dropping implication arrow, and
     adding a "," to separate the domain of quantification from the
     proposition.
   "(a : A) → (b : B) →" interchangeable with "∀ a : A, b : B, "

   Agda's syntax declarations work well but have some limitations and
   restrictions that prevent them from being able to modify the language
   to the form we want. Can't use ∀ or : in a syntax declaration, which
   prevents us from being able to change the "(a : A) → " syntax to
   "∀ a : A ,". We have to use something like "Π a ∈ A ,". 

   The syntax declarations are also pretty rigid, so, the "Π a ∈ A ," syntax
   won't work if you try "Π a b ∈ A ,". This isn't a particularly big problem
   for writing universal quantification expressions because the language
   already allows you to write "(a b : A) →", but it's a bigger problem for
   existentials which have no built-in syntax for this.


3) Should be able to use any fixity for binary operations taken as
   arguments to a function without having to write them as "_+_" or
   make a fixity declaration inside a where clause. Not sure how their
   precedence level should be handled yet but it would be good to
   handle that in a cleaner way.

4) Should use typical ambiguity in order to drop the levels information
   from propositions and proofs

5) When taking functions as arguments you should be able to drop the
   quantifiers over the sets that these functions are between, as it should
   be able to be inferred.

6) Binding custom built-ins to type-theory constructs.

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

-- Identity function
id : ∀ {α}{A : ★ α} → A → A
id x = x

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

{-
data ⊥-level : (α : Level) → ★ α where
ω-level : {A : ★ α} → ⊥-level → A
ω-level ()
-}
--True
data ⊤ : ★₀ where
 ● : ⊤

-- Not
¬ : ∀ {α} → ★ α → ★ α
¬ A = A → ⊥

-- Or
data _∨_ {α β} (A : ★ α) (B : ★ β) : ★ (α ⊔ β) where
 ∨-cons1 : A → A ∨ B
 ∨-cons2 : B → A ∨ B 
infixr 0 _∨_

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


syntax ∃ A (λ x → e) = ∃ x ∈ A , e

π₁ : ∀ {α β} {A : ★ α} {B : A → ★ β} → (∃ x ∈ A , B x) → A
π₁ (x , y) = x

π₂ : ∀ {α β} {A : ★ α} {B : A → ★ β} → (∃AB : ∃ x ∈ A , B x) → B (π₁ ∃AB)
π₂ (x , y) = y



{- use ∃ instead of Σ so that propositions can be read purely logically -}


-- ¬(A∨B) implies ¬(A∧B)  
[¬∨]→[¬∧] : ∀ {α β} (A : ★ α) (B : ★ β) → (¬ (A ∨ B) → ¬ (A ∧ B))
[¬∨]→[¬∧] A B [¬∨] (∧-cons x y) = [¬∨] (∨-cons1 x)

-- (A∧B) implies (A∨B)
∧→∨ : ∀ {α β} {A : ★ α} {B : ★ β} → (A ∧ B → A ∨ B)
∧→∨ {A} {B} (∧-cons x y) = ∨-cons1 x  

∧→∨₂ : ∀ {α β} {A : ★ α} {B : ★ β} → (A ∧ B → A ∨ B)
∧→∨₂ {A} {B} (∧-cons x y) = ∨-cons2 y



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



-- Booleans

data 𝔹 : ★₀ where
 𝕥 : 𝔹
 𝕗 : 𝔹


-- Take a Bool to the corresponding proposition:
𝔹-★ : 𝔹 → ★₀
𝔹-★ 𝕥 = ⊤
𝔹-★ 𝕗 = ⊥

-- Boolean negation
! : 𝔹 → 𝔹
! 𝕥 = 𝕗
! 𝕗 = 𝕥

-- Boolean AND
_&&_ : 𝔹 → 𝔹 → 𝔹
_&&_ 𝕥 𝕥 = 𝕥
_&&_ 𝕥 𝕗 = 𝕗
_&&_ 𝕗 𝕥 = 𝕗
_&&_ 𝕗 𝕗 = 𝕗 


-- Boolean OR
_||_ : 𝔹 → 𝔹 → 𝔹
_||_ 𝕥 𝕥 = 𝕥
_||_ 𝕥 𝕗 = 𝕥
_||_ 𝕗 𝕥 = 𝕥
_||_ 𝕗 𝕗 = 𝕗


-- btw this collection of Boolean functions is functionally complete


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

-- If A = B then A → B
[A=B]→[A→B] : ∀ {α} {A B : ★ α} (p : A ≡ B) → (A → B)
[A=B]→[A→B] {α} {A} {.A} (⟲ .A) x = x


-- thus, ⊤ is not equal to ⊥ 
⊤≠⊥ : ⊤ ≠ ⊥
⊤≠⊥ p = [A=B]→[A→B] p ●



reflexive : ∀ {α β} {A : ★ α} (P : A → ★ β) → ★ (α ⊔ β)
reflexive {α} {β} {A} P = Π x ∈ A , P x 

-- Equality is reflexive
≡-⟲ : ∀ {α} {A : ★ α} (x : A) → x ≡ x
≡-⟲ = ⟲

-- but inequality of course is not
≠-irreflexive : ∀ {α} {A : ★ α} (x : A) → ¬ (x ≠ x)
≠-irreflexive x [x≠x] = ☢
 where
  ☢ : ⊥
  ☢ = [x≠x] (⟲ x)

symmetric : ∀ {α β} {A : ★ α} (P : A → A → ★ β) → ★ (α ⊔ β)
symmetric {α} {β} {A} P = {x y : A} → P x y → P y x 

-- Equality is symmetric
≡-↑↓ : ∀ {α} {A : ★ α} {x y : A} (p : x ≡ y) → y ≡ x
≡-↑↓ (⟲ a) = ⟲ a

-- ... and so is inequality
≠-↑↓ : ∀ {α} {A : ★ α} {a b : A} → a ≠ b → b ≠ a
≠-↑↓ [a≠b] [b≡a] = ☢
 where
  ☢ : ⊥
  ☢ = [a≠b] (≡-↑↓ [b≡a])


transitive : ∀ {α β} {A : ★ α} (P : A → A → ★ β) → ★ (α ⊔ β)
transitive {α} {β} {A} P = {x y z : A} → P x y → P y z → P x z

-- Equality is transitive
≡-⇶ : ∀ {α} {A : ★ α} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
≡-⇶ (⟲ x) (⟲ .x) = ⟲ x

≡-⇶₂ : ∀ {α} {A : ★ α} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
≡-⇶₂ (⟲ x) e = e

-- we'll prove that inequality is not transitive a bit further down

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





structural-invariant : ∀ {α β} (P : ★ α → ★ β) → ★ ((lsuc α) ⊔ β)
structural-invariant {α} {β} P = (A B : ★ α) → A ≅ B → P A → P B

-- Is there any property that's not a structural invariant?
-- https://www.andrew.cmu.edu/user/awodey/preprints/siu.pdf
-- according to this, every property is structurally invariant
-- but is this a logical proof or a metalogical proof?

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
 ∀ {α β} (A B : ★ α) ([A≅B] : A ≅ B) 
 (P : A → ★ β) (a : A) (b : B) → (([A≅B]→[A→B] [A≅B]) a ≡ b) → 
 P a → (P ∘ ([A≅B]→[B→A] [A≅B])) b
≅-Δ A B [A≅B] P a b [fa≡b] Pa = Δ [a≡gb] P Pa    
 where
  f : A → B
  f = [A≅B]→[A→B] [A≅B]
  
  g : B → A
  g = [A≅B]→[B→A] [A≅B]

  a→[gfa≡a] : (a : A) → _≡_ ((g ∘ f) a) a
  a→[gfa≡a] = [A≅B]→[gf≡id] [A≅B]

  [a≡gfa] : _≡_ a ((g ∘ f) a)
  [a≡gfa] = ≡-↑↓ (a→[gfa≡a] a) 

  [gfa≡gb] : _≡_ ((g ∘ f) a) (g b)
  [gfa≡gb] = [a≡b]→[fa≡fb] g (f a) b [fa≡b]
  
  [a≡gb] : _≡_ a (g b)
  [a≡gb] = ≡-⇶ [a≡gfa] [gfa≡gb]
  
  


-- Boolean true is not equal to Boolean false
𝕥≠𝕗 : 𝕥 ≠ 𝕗
𝕥≠𝕗 p = ⊤≠⊥ ([a≡b]→[fa≡fb] 𝔹-★ 𝕥 𝕗 p)



-- No Boolean equals its own negation
a≠!a : ∀ (a : 𝔹) → a ≠ ! a
a≠!a 𝕥 p = ⊤≠⊥ ([a≡b]→[fa≡fb] 𝔹-★ 𝕥 𝕗 p)
a≠!a 𝕗 p = ⊤≠⊥ (≡-↑↓ ([a≡b]→[fa≡fb] 𝔹-★ 𝕗 𝕥 p))


-- The Peano naturals
data ℕ : ★₀ where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ


-- Algebraic data-structures:


-- uniqueness
unique : 
 ∀ {α β} {A : ★ α} (P : A → ★ β) (a : A) → 
 ★ (α ⊔ β)
unique {α} {β} {A} P a = ∀ (a' : A) (p : P a') → a ≡ a'


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



--Latin squares:
LatinRight : ∀ {α} {A : ★ α} (+ : A → A → A) → ★ α
LatinRight {α} {A} +' = ∀ (a b : A) → ∃! x ∈ A , (a + x ≡ b) 
 where 
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_

LatinLeft : ∀ {α} {A : ★ α} (+ : A → A → A) → ★ α
LatinLeft {α} {A} +' = ∀ (a b : A) → ∃! y ∈ A , (y + a ≡ b)
 where
  _+_ : A → A → A
  x + y = +' x y
  infix 2 _+_

LatinSquare : ∀ {α} {A : ★ α} (+ : A → A → A) → ★ α
LatinSquare + = LatinLeft + ∧ LatinRight +



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


{-
record Group : Set ★₁ where
 field
  M : ★₀
  + : M → M → M
  +-id : has-identity +
  +-assoc : is-associative +
  +-inv : has-inverses (record {M = M; + = +; +-id = +-id})

-}


{-
record AbelianGroup : ★₁  where
 field
  G : Group
  +-comm : is-commutative (Group.+ G) 
-}


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


-- addition on Nats
_+_ : ℕ → ℕ → ℕ
𝕫 + y = y
(𝕤 x) + y = 𝕤 (x + y)
infixr 2 _+_

_minus_ : ℕ → ℕ → ℕ
𝕫 minus n = 𝕫
(𝕤 m) minus n = 𝕤 (m minus n)
infix 2 _minus_


isZero : ℕ → 𝔹
isZero 𝕫 = 𝕥
isZero x = 𝕗

𝕤x≠𝕫 : (x : ℕ) → (𝕤 x) ≠ 𝕫
𝕤x≠𝕫 x [𝕤x≡𝕫] = ☢
 where
  [isZero-𝕫≡𝕥] : isZero 𝕫 ≡ 𝕥
  [isZero-𝕫≡𝕥] = ⟲ 𝕥

  [isZero-𝕤x≡𝕗] : isZero (𝕤 x) ≡ 𝕗
  [isZero-𝕤x≡𝕗] = ⟲ 𝕗

  [isZero-𝕫≡isZero-𝕤x] : isZero 𝕫 ≡ isZero (𝕤 x)
  [isZero-𝕫≡isZero-𝕤x] = [f≡g]→[fa≡ga]₂ isZero isZero (⟲ isZero) 𝕫 (𝕤 x) (≡-↑↓ [𝕤x≡𝕫])

  [𝕥≡𝕗] : 𝕥 ≡ 𝕗
  [𝕥≡𝕗] = ≡-⇶ (≡-⇶ (≡-↑↓ [isZero-𝕫≡𝕥]) [isZero-𝕫≡isZero-𝕤x]) [isZero-𝕤x≡𝕗]

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]

𝕫≠𝕤x : (x : ℕ) → 𝕫 ≠ (𝕤 x)
𝕫≠𝕤x x = ≠-↑↓ (𝕤x≠𝕫 x)

¬[≠-⇶] : (∀ {α} {A : ★ α} {x y z : A} (p : x ≠ y) (q : y ≠ z) → x ≠ z) → ⊥
¬[≠-⇶] hyp = ☢
 where
  ☢ : ⊥
  ☢ = hyp (𝕫≠𝕤x 𝕫) (𝕤x≠𝕫 𝕫) (⟲ 𝕫)


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

x<y→x≤y : (x y : ℕ) → x < y → x ≤ y
x<y→x≤y x y (a , (b , (∧-cons [𝕤b≡a] [x+a≡y]))) = (a , [x+a≡y])

x>y→x≥y : (x y : ℕ) → x > y → x ≥ y
x>y→x≥y x y (a , (b , (∧-cons [𝕤b≡a] [y+a≡x]))) = (a , [y+a≡x])

𝕫+x≡x : (x : ℕ) → 𝕫 + x ≡ x
𝕫+x≡x n = ⟲ n

[x+𝕫≡x]→[𝕤x+𝕫≡𝕤x] : (x : ℕ) → (x + 𝕫 ≡ x) → (𝕤 x + 𝕫 ≡ 𝕤 x)
[x+𝕫≡x]→[𝕤x+𝕫≡𝕤x] x [x+𝕫≡x] = [a≡b]→[fa≡fb] 𝕤 (x + 𝕫) x [x+𝕫≡x] 

x+𝕫≡x : (x : ℕ) → x + 𝕫 ≡ x
x+𝕫≡x 𝕫 = ⟲ 𝕫
x+𝕫≡x (𝕤 n) = [x+𝕫≡x]→[𝕤x+𝕫≡𝕤x] n (x+𝕫≡x n)

x≥𝕫 : (x : ℕ) → x ≥ 𝕫
x≥𝕫 x = (x , 𝕫+x≡x x)

𝕤𝕫+x≡𝕤x : (x : ℕ) → (𝕤 𝕫) + x ≡ 𝕤 x
𝕤𝕫+x≡𝕤x x = ⟲ (𝕤 x)

𝕤x+y≡𝕤[x+y] : (x y : ℕ) → (𝕤 x) + y ≡ 𝕤 (x + y)
𝕤x+y≡𝕤[x+y] x y = ⟲ (𝕤 (x + y))

+-comm-base : (n : ℕ) → n + 𝕫 ≡ 𝕫 + n
+-comm-base n = [n+𝕫≡𝕫+n]
 where
  [n+𝕫≡n] : n + 𝕫 ≡ n
  [n+𝕫≡n] = x+𝕫≡x n
 
  [n≡𝕫+n] : n ≡ 𝕫 + n
  [n≡𝕫+n] = ≡-↑↓ (𝕫+x≡x n)

  [n+𝕫≡𝕫+n] = ≡-⇶ [n+𝕫≡n] [n≡𝕫+n] 


𝕫+𝕤𝕫≡𝕤𝕫 : 𝕫 + (𝕤 𝕫) ≡ (𝕤 𝕫)
𝕫+𝕤𝕫≡𝕤𝕫 = ⟲ (𝕤 𝕫)


[x+𝕤𝕫≡𝕤x]→[𝕤x+𝕤𝕫≡𝕤𝕤x] : (x : ℕ) → x + (𝕤 𝕫) ≡ 𝕤 x → (𝕤 x) + (𝕤 𝕫) ≡ 𝕤 (𝕤 x)
[x+𝕤𝕫≡𝕤x]→[𝕤x+𝕤𝕫≡𝕤𝕤x] x [x+𝕤𝕫≡𝕤x] = [𝕤x+𝕤𝕫≡𝕤𝕤x]
 where
  [𝕤x+𝕤𝕫≡𝕤[x+𝕤𝕫]] : (𝕤 x) + (𝕤 𝕫) ≡ 𝕤 (x + (𝕤 𝕫))
  [𝕤x+𝕤𝕫≡𝕤[x+𝕤𝕫]] = 𝕤x+y≡𝕤[x+y] x (𝕤 𝕫)

  [𝕤[x+𝕤𝕫]≡𝕤𝕤x] : 𝕤 (x + 𝕤 𝕫) ≡ 𝕤 (𝕤 x)
  [𝕤[x+𝕤𝕫]≡𝕤𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (x + 𝕤 𝕫) (𝕤 x) [x+𝕤𝕫≡𝕤x] 

  [𝕤x+𝕤𝕫≡𝕤𝕤x] : (𝕤 x) + (𝕤 𝕫) ≡ 𝕤 (𝕤 x)
  [𝕤x+𝕤𝕫≡𝕤𝕤x] = ≡-⇶ [𝕤x+𝕤𝕫≡𝕤[x+𝕤𝕫]] [𝕤[x+𝕤𝕫]≡𝕤𝕤x]

x+𝕤𝕫≡𝕤x : (x : ℕ) → x + (𝕤 𝕫) ≡ 𝕤 x
x+𝕤𝕫≡𝕤x 𝕫 = 𝕫+𝕤𝕫≡𝕤𝕫
x+𝕤𝕫≡𝕤x (𝕤 n) = [x+𝕤𝕫≡𝕤x]→[𝕤x+𝕤𝕫≡𝕤𝕤x] n (x+𝕤𝕫≡𝕤x n)


𝕤[x+𝕫]≡x+𝕤𝕫 : (x : ℕ) → 𝕤 (x + 𝕫) ≡ x + (𝕤 𝕫)
𝕤[x+𝕫]≡x+𝕤𝕫 x = proof
 where
  [x+𝕫≡x] : x + 𝕫 ≡ x
  [x+𝕫≡x] = x+𝕫≡x x
  
  [𝕤[x+𝕫]≡𝕤x] : 𝕤 (x + 𝕫) ≡ 𝕤 x
  [𝕤[x+𝕫]≡𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (x + 𝕫) x [x+𝕫≡x]
  
  [𝕤x≡x+𝕤𝕫] : 𝕤 x ≡ x + (𝕤 𝕫)
  [𝕤x≡x+𝕤𝕫] = ≡-↑↓ (x+𝕤𝕫≡𝕤x x) 

  proof : 𝕤 (x + 𝕫) ≡ x + (𝕤 𝕫)
  proof = ≡-⇶ [𝕤[x+𝕫]≡𝕤x] [𝕤x≡x+𝕤𝕫]

𝕤[𝕫+y]≡𝕫+𝕤y : (y : ℕ) → 𝕤 (𝕫 + y) ≡ 𝕫 + (𝕤 y)
𝕤[𝕫+y]≡𝕫+𝕤y y = ⟲ (𝕤 y)

[𝕤[𝕫+y]≡𝕫+𝕤y]→[𝕤[𝕫+𝕤y]≡𝕫+𝕤𝕤y] : (y : ℕ) → 𝕤 (𝕫 + y) ≡ 𝕫 + (𝕤 y) → 𝕤 (𝕫 + (𝕤 y)) ≡ 𝕫 + (𝕤 (𝕤 y))
[𝕤[𝕫+y]≡𝕫+𝕤y]→[𝕤[𝕫+𝕤y]≡𝕫+𝕤𝕤y] y [𝕤[𝕫+y]≡𝕫+𝕤y] = [𝕤[𝕫+𝕤y]≡𝕫+𝕤𝕤y]
 where
  [𝕤[𝕫+𝕤y]≡𝕫+𝕤𝕤y] : 𝕤 (𝕫 + (𝕤 y)) ≡ 𝕫 + (𝕤 (𝕤 y))
  [𝕤[𝕫+𝕤y]≡𝕫+𝕤𝕤y] = 𝕤[𝕫+y]≡𝕫+𝕤y (𝕤 y)


{-
[[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]]→[[𝕤[𝕤x+y]≡𝕤x+𝕤y]→[𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]] :
 ((x y : ℕ) → (𝕤 (x + y) ≡ x + (𝕤 y)) → (𝕤 (x + 𝕤 y) ≡ x + 𝕤 (𝕤 y))) →
 (x y : ℕ) → (𝕤 ((𝕤 x) + y) ≡ (𝕤 x) + (𝕤 y)) → (𝕤 ((𝕤 x) + (𝕤 y)) ≡ (𝕤 x) + 𝕤 (𝕤 y))

[[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]]→[[𝕤[𝕤x+y]≡𝕤x+𝕤y]→[𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]] 
 [[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]]
 x y 
 [𝕤[𝕤x+y]≡𝕤x+𝕤y]
 
 = [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]

  where
   [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y] : 𝕤 ((𝕤 x) + (𝕤 y)) ≡ (𝕤 x) + 𝕤 (𝕤 y)
   [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y] = [[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]] (𝕤 x) y [𝕤[𝕤x+y]≡𝕤x+𝕤y]
-}


pred : ℕ → ℕ
pred 𝕫 = 𝕫
pred (𝕤 n) = n

pred-𝕤n≡n : (n : ℕ) → pred (𝕤 n) ≡ n
pred-𝕤n≡n n = ⟲ n

[𝕤x≡𝕤y]→[x≡y] : (x y : ℕ) → (𝕤 x) ≡ (𝕤 y) → x ≡ y
[𝕤x≡𝕤y]→[x≡y] x y [𝕤x≡𝕤y] = [a≡b]→[fa≡fb] pred (𝕤 x) (𝕤 y) [𝕤x≡𝕤y]


[[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]]→[[𝕤[𝕤x+y]≡𝕤x+𝕤y]→[𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]] :
 (x : ℕ) →
 ((y : ℕ) → (𝕤 (x + y) ≡ x + (𝕤 y)) → (𝕤 (x + (𝕤 y)) ≡ x + (𝕤 (𝕤 y)))) →
  (y : ℕ) → (𝕤 ((𝕤 x) + y) ≡ (𝕤 x) + (𝕤 y)) → (𝕤 ((𝕤 x) + (𝕤 y)) ≡ (𝕤 x) + (𝕤 (𝕤 y)))

[[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]]→[[𝕤[𝕤x+y]≡𝕤x+𝕤y]→[𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]] 
 x
 [[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]]
 y
 [𝕤[𝕤x+y]≡𝕤x+𝕤y]
 
 = [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]

 where
    
  [𝕤x+𝕤y≡𝕤[x+𝕤y]] : (𝕤 x) + (𝕤 y) ≡ 𝕤 (x + (𝕤 y))
  [𝕤x+𝕤y≡𝕤[x+𝕤y]] = 𝕤x+y≡𝕤[x+y] x (𝕤 y)
 
  [𝕤[𝕤x+𝕤y]≡𝕤[𝕤[x+𝕤y]]] : 𝕤 ((𝕤 x) + (𝕤 y)) ≡ 𝕤 (𝕤 (x + 𝕤 y))
  [𝕤[𝕤x+𝕤y]≡𝕤[𝕤[x+𝕤y]]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((𝕤 x) + (𝕤 y)) (𝕤 (x + 𝕤 y)) [𝕤x+𝕤y≡𝕤[x+𝕤y]]
 
  [[𝕤[𝕤[𝕤x+y]]]≡𝕤[𝕤x+𝕤y]] : (𝕤 (𝕤 ((𝕤 x) + y))) ≡ (𝕤 ((𝕤 x) + (𝕤 y)))
  [[𝕤[𝕤[𝕤x+y]]]≡𝕤[𝕤x+𝕤y]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (𝕤 ((𝕤 x) + y)) ((𝕤 x) + (𝕤 y)) [𝕤[𝕤x+y]≡𝕤x+𝕤y]

  [𝕤𝕤𝕤[x+y]≡𝕤𝕤[𝕤x+y]] : (𝕤 (𝕤 (𝕤 (x + y)))) ≡ 𝕤 (𝕤 ((𝕤 x) + y))
  [𝕤𝕤𝕤[x+y]≡𝕤𝕤[𝕤x+y]] = [f≡g]→[fa≡ga]₂ (𝕤 ∘ 𝕤) (𝕤 ∘ 𝕤) (⟲ (𝕤 ∘ 𝕤)) (𝕤 (x + y)) ((𝕤 x) + y) (≡-↑↓ (𝕤x+y≡𝕤[x+y] x y)) 

  [𝕤𝕤𝕤[x+y]≡𝕤[𝕤x+𝕤y]] : (𝕤 (𝕤 (𝕤 (x + y)))) ≡ (𝕤 ((𝕤 x) + (𝕤 y)))
  [𝕤𝕤𝕤[x+y]≡𝕤[𝕤x+𝕤y]] = ≡-⇶ [𝕤𝕤𝕤[x+y]≡𝕤𝕤[𝕤x+y]] [[𝕤[𝕤[𝕤x+y]]]≡𝕤[𝕤x+𝕤y]]
  
  [𝕤𝕤𝕤[x+y]≡𝕤𝕤[x+𝕤y]]] : (𝕤 (𝕤 (𝕤 (x + y)))) ≡ (𝕤 (𝕤 (x + (𝕤 y))))
  [𝕤𝕤𝕤[x+y]≡𝕤𝕤[x+𝕤y]]] = ≡-⇶ [𝕤𝕤𝕤[x+y]≡𝕤[𝕤x+𝕤y]] [𝕤[𝕤x+𝕤y]≡𝕤[𝕤[x+𝕤y]]] 

  [𝕤𝕤[x+y]≡𝕤[x+𝕤y]] : (𝕤 (𝕤 (x + y))) ≡ (𝕤 (x + (𝕤 y)))
  [𝕤𝕤[x+y]≡𝕤[x+𝕤y]] = [𝕤x≡𝕤y]→[x≡y] (𝕤 (𝕤 (x + y))) (𝕤 (x + (𝕤 y))) [𝕤𝕤𝕤[x+y]≡𝕤𝕤[x+𝕤y]]]
 
  [𝕤[x+y]≡x+𝕤y] : (𝕤 (x + y)) ≡ x + (𝕤 y)
  [𝕤[x+y]≡x+𝕤y] = [𝕤x≡𝕤y]→[x≡y] (𝕤 (x + y)) (x + (𝕤 y)) [𝕤𝕤[x+y]≡𝕤[x+𝕤y]]
  
  [𝕤[x+𝕤y]≡x+𝕤𝕤y] : (𝕤 (x + (𝕤 y))) ≡ x + (𝕤 (𝕤 y)) 
  [𝕤[x+𝕤y]≡x+𝕤𝕤y] = [[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y]] y [𝕤[x+y]≡x+𝕤y]

  [𝕤𝕤[x+y]≡x+𝕤𝕤y] : (𝕤 (𝕤 (x + y))) ≡ x + (𝕤 (𝕤 y))
  [𝕤𝕤[x+y]≡x+𝕤𝕤y] = ≡-⇶ [𝕤𝕤[x+y]≡𝕤[x+𝕤y]] [𝕤[x+𝕤y]≡x+𝕤𝕤y]

  [𝕤𝕤𝕤[x+y]≡𝕤[x+𝕤𝕤y]] : (𝕤 (𝕤 (𝕤 (x + y)))) ≡ (𝕤 x) + (𝕤 (𝕤 y))
  [𝕤𝕤𝕤[x+y]≡𝕤[x+𝕤𝕤y]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (𝕤 (𝕤 (x + y))) (x + (𝕤 (𝕤 y))) [𝕤𝕤[x+y]≡x+𝕤𝕤y]
  

  [𝕤[x+𝕤𝕤y]≡𝕤x+𝕤𝕤y] : (𝕤 (x + (𝕤 (𝕤 y)))) ≡ (𝕤 x) + (𝕤 (𝕤 y))
  [𝕤[x+𝕤𝕤y]≡𝕤x+𝕤𝕤y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x (𝕤 (𝕤 y)))
 
  [𝕤𝕤𝕤[x+y]≡𝕤x+𝕤𝕤y]] : (𝕤 (𝕤 (𝕤 (x + y)))) ≡ 𝕤 (x + (𝕤 (𝕤 y)))
  [𝕤𝕤𝕤[x+y]≡𝕤x+𝕤𝕤y]] = ≡-⇶ [𝕤𝕤𝕤[x+y]≡𝕤[x+𝕤𝕤y]] [𝕤[x+𝕤𝕤y]≡𝕤x+𝕤𝕤y]
  
  [𝕤[𝕤x+𝕤y]≡𝕤𝕤𝕤[x+y]] : (𝕤 ((𝕤 x) + (𝕤 y))) ≡ (𝕤 (𝕤 (𝕤 (x + y))))
  [𝕤[𝕤x+𝕤y]≡𝕤𝕤𝕤[x+y]] = ≡-↑↓ [𝕤𝕤𝕤[x+y]≡𝕤[𝕤x+𝕤y]]
  
  [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y] : (𝕤 ((𝕤 x) + (𝕤 y))) ≡ (𝕤 x) + (𝕤 (𝕤 y))
  [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y] = ≡-⇶ [𝕤[𝕤x+𝕤y]≡𝕤𝕤𝕤[x+y]] [𝕤𝕤𝕤[x+y]≡𝕤x+𝕤𝕤y]]







[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y] : (x y : ℕ) → 𝕤 (x + y) ≡ x + (𝕤 y) → 𝕤 (x + 𝕤 y) ≡ x + 𝕤 (𝕤 y)
[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y] 𝕫 y p = 𝕤[𝕫+y]≡𝕫+𝕤y (𝕤 y)
[𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y] (𝕤 x) y [𝕤[𝕤x+y]≡𝕤x+𝕤y] = [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y]
 where
 [𝕤[𝕤x+y]≡𝕤𝕤[x+y]] : (𝕤 ((𝕤 x) + y)) ≡ (𝕤 (𝕤 (x + y)))
 [𝕤[𝕤x+y]≡𝕤𝕤[x+y]] = 𝕤x+y≡𝕤[x+y] (𝕤 x) y 

 [𝕤𝕤[x+y]≡[𝕤[𝕤x+y]] : (𝕤 (𝕤 (x + y))) ≡ (𝕤 ((𝕤 x) + y))
 [𝕤𝕤[x+y]≡[𝕤[𝕤x+y]] = ≡-↑↓ [𝕤[𝕤x+y]≡𝕤𝕤[x+y]]

 [𝕤x+𝕤y≡𝕤[x+𝕤y]] : (𝕤 x) + (𝕤 y) ≡ (𝕤 (x + (𝕤 y)))
 [𝕤x+𝕤y≡𝕤[x+𝕤y]] = 𝕤x+y≡𝕤[x+y] x (𝕤 y) 
 
 
 [𝕤[x+𝕤y]≡𝕤x+𝕤y] : (𝕤 (x + (𝕤 y))) ≡ (𝕤 x) + (𝕤 y)
 [𝕤[x+𝕤y]≡𝕤x+𝕤y] = ≡-↑↓ [𝕤x+𝕤y≡𝕤[x+𝕤y]]

 [𝕤𝕤[x+y]≡𝕤x+𝕤y] : (𝕤 (𝕤 (x + y))) ≡ (𝕤 x) + (𝕤 y)
 [𝕤𝕤[x+y]≡𝕤x+𝕤y] = ≡-⇶ [𝕤𝕤[x+y]≡[𝕤[𝕤x+y]] [𝕤[𝕤x+y]≡𝕤x+𝕤y]

 [𝕤𝕤[x+y]≡𝕤[x+𝕤y]] : (𝕤 (𝕤 (x + y))) ≡ (𝕤 (x + (𝕤 y)))
 [𝕤𝕤[x+y]≡𝕤[x+𝕤y]] = ≡-⇶ [𝕤𝕤[x+y]≡𝕤x+𝕤y] [𝕤x+𝕤y≡𝕤[x+𝕤y]]

 [𝕤[x+y]≡[x+𝕤y]] : (𝕤 (x + y)) ≡ x + (𝕤 y)
 [𝕤[x+y]≡[x+𝕤y]] = [𝕤x≡𝕤y]→[x≡y] (𝕤 (x + y)) (x + (𝕤 y)) [𝕤𝕤[x+y]≡𝕤[x+𝕤y]]
 
 [𝕤[x+𝕤y]≡x+𝕤𝕤y] : (𝕤 (x + (𝕤 y))) ≡ x + (𝕤 (𝕤 y))
 [𝕤[x+𝕤y]≡x+𝕤𝕤y] = [𝕤[x+y]≡x+𝕤y]→[𝕤[x+𝕤y]≡x+𝕤𝕤y] x y [𝕤[x+y]≡[x+𝕤y]]

 [𝕤x+𝕤y≡x+𝕤𝕤y] : (𝕤 x) + (𝕤 y) ≡ x + (𝕤 (𝕤 y))
 [𝕤x+𝕤y≡x+𝕤𝕤y] = ≡-⇶ [𝕤x+𝕤y≡𝕤[x+𝕤y]] [𝕤[x+𝕤y]≡x+𝕤𝕤y]

 [𝕤[𝕤x+𝕤y]≡𝕤[x+𝕤𝕤y]] : (𝕤 ((𝕤 x) + (𝕤 y))) ≡ (𝕤 (x + (𝕤 (𝕤 y))))
 [𝕤[𝕤x+𝕤y]≡𝕤[x+𝕤𝕤y]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((𝕤 x) + (𝕤 y)) (x + (𝕤 (𝕤 y))) [𝕤x+𝕤y≡x+𝕤𝕤y]

 [𝕤[x+𝕤𝕤y]≡𝕤x+𝕤𝕤y] : (𝕤 (x + (𝕤 (𝕤 y)))) ≡ (𝕤 x) + (𝕤 (𝕤 y))
 [𝕤[x+𝕤𝕤y]≡𝕤x+𝕤𝕤y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x (𝕤 (𝕤 y)))  
 

 [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y] : (𝕤 ((𝕤 x) + (𝕤 y))) ≡ (𝕤 x) + (𝕤 (𝕤 y))
 [𝕤[𝕤x+𝕤y]≡𝕤x+𝕤𝕤y] = ≡-⇶ [𝕤[𝕤x+𝕤y]≡𝕤[x+𝕤𝕤y]] [𝕤[x+𝕤𝕤y]≡𝕤x+𝕤𝕤y]


[𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y] : 
 (y : ℕ) → 
 ((x : ℕ) → (𝕤 (x + y)) ≡ x + (𝕤 y)) →
 (x : ℕ) → (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y) 
[𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y]
 y
 x→[𝕤[x+y]≡x+𝕤y]
 x
 = [𝕤[𝕤x+y]≡𝕤x+𝕤y]
  where 
   [𝕤[x+y]≡x+𝕤y] : (𝕤 (x + y)) ≡ x + (𝕤 y)
   [𝕤[x+y]≡x+𝕤y] = x→[𝕤[x+y]≡x+𝕤y] x

   [𝕤x+y≡𝕤[x+y]] : (𝕤 x) + y ≡ (𝕤 (x + y))
   [𝕤x+y≡𝕤[x+y]] = 𝕤x+y≡𝕤[x+y] x y

   [𝕤x+y≡x+𝕤y] : (𝕤 x) + y ≡ x + (𝕤 y)
   [𝕤x+y≡x+𝕤y] = ≡-⇶ [𝕤x+y≡𝕤[x+y]] [𝕤[x+y]≡x+𝕤y]

   [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] : (𝕤 ((𝕤 x) + y)) ≡ (𝕤 ( x + (𝕤 y)))
   [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((𝕤 x) + y) ( x + (𝕤 y)) [𝕤x+y≡x+𝕤y]

   [𝕤[x+𝕤y]≡𝕤x+𝕤y] : (𝕤 (x + (𝕤 y))) ≡ (𝕤 x) + (𝕤 y)
   [𝕤[x+𝕤y]≡𝕤x+𝕤y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x (𝕤 y))   

   [𝕤[𝕤x+y]≡𝕤x+𝕤y] :  (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
   [𝕤[𝕤x+y]≡𝕤x+𝕤y] = ≡-⇶ [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] [𝕤[x+𝕤y]≡𝕤x+𝕤y]

[𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y]₂ :
 (x y : ℕ) → 
 (𝕤 (x + y)) ≡ x + (𝕤 y) →
 (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
[𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y]₂ x y [𝕤[x+y]≡x+𝕤y] = [𝕤[𝕤x+y]≡𝕤x+𝕤y] 
 where
   [𝕤x+y≡𝕤[x+y]] : (𝕤 x) + y ≡ (𝕤 (x + y))
   [𝕤x+y≡𝕤[x+y]] = 𝕤x+y≡𝕤[x+y] x y

   [𝕤x+y≡x+𝕤y] : (𝕤 x) + y ≡ x + (𝕤 y)
   [𝕤x+y≡x+𝕤y] = ≡-⇶ [𝕤x+y≡𝕤[x+y]] [𝕤[x+y]≡x+𝕤y]

   [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] : (𝕤 ((𝕤 x) + y)) ≡ (𝕤 ( x + (𝕤 y)))
   [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((𝕤 x) + y) ( x + (𝕤 y)) [𝕤x+y≡x+𝕤y]

   [𝕤[x+𝕤y]≡𝕤x+𝕤y] : (𝕤 (x + (𝕤 y))) ≡ (𝕤 x) + (𝕤 y)
   [𝕤[x+𝕤y]≡𝕤x+𝕤y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x (𝕤 y))   

   [𝕤[𝕤x+y]≡𝕤x+𝕤y] :  (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
   [𝕤[𝕤x+y]≡𝕤x+𝕤y] = ≡-⇶ [𝕤[𝕤x+y]≡𝕤[x+𝕤y]] [𝕤[x+𝕤y]≡𝕤x+𝕤y]

  

𝕤[x+y]≡x+𝕤y : (x y : ℕ) → 𝕤 (x + y) ≡ x + (𝕤 y)
𝕤[x+y]≡x+𝕤y 𝕫 y  = 𝕤[𝕫+y]≡𝕫+𝕤y y
𝕤[x+y]≡x+𝕤y (𝕤 x) y = [𝕤[𝕤x+y]≡𝕤x+𝕤y]
 where
  [𝕤[𝕤x+y]≡𝕤x+𝕤y] : (𝕤 ((𝕤 x) + y)) ≡ (𝕤 x) + (𝕤 y)
  [𝕤[𝕤x+y]≡𝕤x+𝕤y] = [𝕤[x+y]≡x+𝕤y]→[𝕤[𝕤x+y]≡𝕤x+𝕤y]₂ x y (𝕤[x+y]≡x+𝕤y x y)

𝕤x+y≡x+𝕤y : (x y : ℕ) → (𝕤 x) + y ≡ x + (𝕤 y)
𝕤x+y≡x+𝕤y x y = ≡-⇶ (𝕤x+y≡𝕤[x+y] x y) (𝕤[x+y]≡x+𝕤y x y)

[𝕤n+x]+y≡[n+x]+𝕤y : (x y n : ℕ) → ((𝕤 n) + x) + y ≡ (n + x) + 𝕤 y
[𝕤n+x]+y≡[n+x]+𝕤y x y n = [[𝕤n+x]+y≡[n+x]+𝕤y]
 where
 [𝕤n+x]≡𝕤[n+x] : (𝕤 n) + x ≡ 𝕤 (n + x)
 [𝕤n+x]≡𝕤[n+x] = 𝕤x+y≡𝕤[x+y] n x

 _⊗_ : ℕ → ℕ → ℕ
 x ⊗ y = y + x
 infix 2 _⊗_

 [[𝕤n+x]+y≡𝕤[n+x]+y] : ((𝕤 n) + x) + y ≡ (𝕤 (n + x)) + y
 [[𝕤n+x]+y≡𝕤[n+x]+y] = [f≡g]→[fa≡ga]₂ (_⊗_ y)  (_⊗_ y) (⟲ (_⊗_ y)) ((𝕤 n) + x) (𝕤 (n + x)) [𝕤n+x]≡𝕤[n+x]
 

 [𝕤[n+x]+y≡[n+x]+𝕤y] : (𝕤 (n + x)) + y ≡ (n + x) + (𝕤 y)
 [𝕤[n+x]+y≡[n+x]+𝕤y] = 𝕤x+y≡x+𝕤y (n + x) y

 [[𝕤n+x]+y≡[n+x]+𝕤y] : ((𝕤 n) + x) + y ≡ (n + x) + (𝕤 y)
 [[𝕤n+x]+y≡[n+x]+𝕤y] = ≡-⇶ [[𝕤n+x]+y≡𝕤[n+x]+y] [𝕤[n+x]+y≡[n+x]+𝕤y] 




-- Lemma 
[[a+x]+y≡x+[a+y]]→[[𝕤a+x]+y≡x+[𝕤a+y]] : (x y a : ℕ) → (a + x) + y ≡ x + (a + y) → ((𝕤 a) + x) + y ≡ x + ((𝕤 a) + y)
[[a+x]+y≡x+[a+y]]→[[𝕤a+x]+y≡x+[𝕤a+y]] x y a [[a+x]+y≡x+[a+y]] = [[𝕤a+x]+y≡x+[𝕤a+y]]
 where
  [𝕤[[a+x]+y]≡[𝕤[a+x]]+y] : (𝕤 ((a + x) + y)) ≡ (𝕤 (a + x)) + y
  [𝕤[[a+x]+y]≡[𝕤[a+x]]+y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] (a + x) y) 

  [𝕤[a+x]+y≡𝕤[[a+x]+y]] : (𝕤 (a + x)) + y ≡ (𝕤 ((a + x) + y))
  [𝕤[a+x]+y≡𝕤[[a+x]+y]] = ≡-↑↓ [𝕤[[a+x]+y]≡[𝕤[a+x]]+y]

  [𝕤[a+x]≡𝕤a+x] : (𝕤 (a + x)) ≡ (𝕤 a) + x
  [𝕤[a+x]≡𝕤a+x] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] a x)

  _⊕_ : ℕ → ℕ → ℕ
  x ⊕ y = y + x
  infix 2 _⊕_ 

  [𝕤[a+x]+y≡[𝕤a+x]+y] : (𝕤 (a + x)) + y ≡ ((𝕤 a) + x) + y
  [𝕤[a+x]+y≡[𝕤a+x]+y] = [f≡g]→[fa≡ga]₂ (_⊕_ y) (_⊕_ y) (⟲ (_⊕_ y))  (𝕤 (a + x)) ((𝕤 a) + x) [𝕤[a+x]≡𝕤a+x]

  [[𝕤a+x]+y≡𝕤[a+x]+y] : ((𝕤 a) + x) + y ≡ (𝕤 (a + x)) + y
  [[𝕤a+x]+y≡𝕤[a+x]+y] = ≡-↑↓ [𝕤[a+x]+y≡[𝕤a+x]+y]

  [[𝕤a+x]+y≡𝕤[[a+x]+y]] : ((𝕤 a) + x) + y ≡ (𝕤 ((a + x) + y))
  [[𝕤a+x]+y≡𝕤[[a+x]+y]] = ≡-⇶ [[𝕤a+x]+y≡𝕤[a+x]+y] [𝕤[a+x]+y≡𝕤[[a+x]+y]]

  [𝕤[x+[a+y]]≡𝕤x+[a+y]] : (𝕤 (x + (a + y))) ≡ (𝕤 x) + (a + y)
  [𝕤[x+[a+y]]≡𝕤x+[a+y]] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x (a + y))
  
  [𝕤x+[a+y]≡x+𝕤[a+y]] : (𝕤 x) + (a + y) ≡ x + (𝕤 (a + y))
  [𝕤x+[a+y]≡x+𝕤[a+y]] = 𝕤x+y≡x+𝕤y x (a + y)

  [x+𝕤[a+y]≡x+[𝕤a+y]] : x + (𝕤 (a + y)) ≡ x + ((𝕤 a) + y)
  [x+𝕤[a+y]≡x+[𝕤a+y]] = [f≡g]→[fa≡ga]₂ (_+_ x) (_+_ x) (⟲ (_+_ x)) (𝕤 (a + y)) ((𝕤 a) + y) (≡-↑↓ (𝕤x+y≡𝕤[x+y] a y))
 
  [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] : (𝕤 ((a + x) + y)) ≡ (𝕤 (x + (a + y)))
  [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) ((a + x) + y) (x + (a + y)) [[a+x]+y≡x+[a+y]]

  [[𝕤a+x]+y≡𝕤[x+[a+y]]] : ((𝕤 a) + x) + y ≡ (𝕤 (x + (a + y)))
  [[𝕤a+x]+y≡𝕤[x+[a+y]]] = ≡-⇶ [[𝕤a+x]+y≡𝕤[[a+x]+y]] [𝕤[[a+x]+y]≡𝕤[x+[a+y]]]
 
  [[𝕤a+x]+y≡𝕤x+[a+y]] : ((𝕤 a) + x) + y ≡ (𝕤 x) + (a + y)
  [[𝕤a+x]+y≡𝕤x+[a+y]] = ≡-⇶ [[𝕤a+x]+y≡𝕤[x+[a+y]]] [𝕤[x+[a+y]]≡𝕤x+[a+y]]

  [[𝕤a+x]+y≡x+𝕤[a+y]] : ((𝕤 a) + x) + y ≡ x + (𝕤 (a + y))
  [[𝕤a+x]+y≡x+𝕤[a+y]] = ≡-⇶ [[𝕤a+x]+y≡𝕤x+[a+y]] [𝕤x+[a+y]≡x+𝕤[a+y]]

  [[𝕤a+x]+y≡x+[𝕤a+y]] : ((𝕤 a) + x) + y ≡ x + ((𝕤 a) + y)
  [[𝕤a+x]+y≡x+[𝕤a+y]] = ≡-⇶ [[𝕤a+x]+y≡x+𝕤[a+y]] [x+𝕤[a+y]≡x+[𝕤a+y]]



[a+x]+y≡x+[a+y] : (x y a : ℕ) → (a + x) + y ≡ x + (a + y)
[a+x]+y≡x+[a+y] x y 𝕫 = ⟲ (x + y)
[a+x]+y≡x+[a+y] x y (𝕤 n) = [[a+x]+y≡x+[a+y]]→[[𝕤a+x]+y≡x+[𝕤a+y]] x y n ([a+x]+y≡x+[a+y] x y n)

x+y≡y+x : (x y : ℕ) → x + y ≡ y + x
x+y≡y+x x y = [x+y≡y+x]
 where
  [[y+x]+𝕫≡x+[y+𝕫]] : (y + x) + 𝕫 ≡ x + (y + 𝕫)
  [[y+x]+𝕫≡x+[y+𝕫]] = [a+x]+y≡x+[a+y] x 𝕫 y

  [[y+x]+𝕫≡y+x] : (y + x) + 𝕫 ≡ y + x
  [[y+x]+𝕫≡y+x] = x+𝕫≡x (y + x)
 
  [y+𝕫≡y] : y + 𝕫 ≡ y
  [y+𝕫≡y] = x+𝕫≡x y

  [x+[y+𝕫]≡x+y] : x + (y + 𝕫) ≡ x + y
  [x+[y+𝕫]≡x+y] = [f≡g]→[fa≡ga]₂ (_+_ x) (_+_ x) (⟲ (_+_ x)) (y + 𝕫) y [y+𝕫≡y]

  [x+[y+𝕫]≡y+x] : x + (y + 𝕫) ≡ y + x
  [x+[y+𝕫]≡y+x] = ≡-⇶ (≡-↑↓ [[y+x]+𝕫≡x+[y+𝕫]]) [[y+x]+𝕫≡y+x]
  
  [x+y≡y+x] : x + y ≡ y + x
  [x+y≡y+x] = ≡-⇶ (≡-↑↓ [x+[y+𝕫]≡x+y]) [x+[y+𝕫]≡y+x]

[a+b]+c≡a+[b+c] : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
[a+b]+c≡a+[b+c] a b c = [[a+b]+c≡a+[b+c]]
 where
  [b+a≡a+b] : b + a ≡ a + b
  [b+a≡a+b] = x+y≡y+x b a

  _⊕_ : ℕ → ℕ → ℕ
  x ⊕ y = y + x
  infix 2 _⊕_

  [[b+a]+c≡[a+b]+c] : (b + a) + c ≡ (a + b) + c
  [[b+a]+c≡[a+b]+c] = [f≡g]→[fa≡ga]₂ (_⊕_ c) (_⊕_ c) (⟲ (_⊕_ c)) (b + a) (a + b) [b+a≡a+b]  

  [[b+a]+c≡a+[b+c]] : (b + a) + c ≡ a + (b + c)
  [[b+a]+c≡a+[b+c]] = [a+x]+y≡x+[a+y] a c b
  

  [[a+b]+c≡a+[b+c]] : (a + b) + c ≡ a + (b + c)
  [[a+b]+c≡a+[b+c]] = ≡-⇶ (≡-↑↓ [[b+a]+c≡[a+b]+c]) [[b+a]+c≡a+[b+c]]


 
{-
[x+𝕤𝕫]≡[𝕤x] : (x : ℕ) → x + (𝕤 𝕫) ≡ 𝕤 x
[x+𝕤𝕫]≡[𝕤x] 𝕫 = 
-}



𝕤𝕫>𝕫 : 𝕤 𝕫 > 𝕫
𝕤𝕫>𝕫 = (𝕤 𝕫 , (𝕫 , ∧-cons (⟲ (𝕤 𝕫)) [[𝕫+𝕤𝕫]≡𝕤𝕫]))
 where
  [[𝕫+𝕤𝕫]≡𝕤𝕫] : 𝕫 + (𝕤 𝕫) ≡ (𝕤 𝕫)
  [[𝕫+𝕤𝕫]≡𝕤𝕫] = 𝕫+x≡x (𝕤 𝕫)   

𝕤x>x : (x : ℕ) → 𝕤 x > x
𝕤x>x x = (𝕤 𝕫 , (𝕫 , (∧-cons (⟲ (𝕤 𝕫)) (x+𝕤𝕫≡𝕤x x))))

x<𝕤x : (x : ℕ) → x < 𝕤 x
x<𝕤x x = (𝕤 𝕫 , (𝕫 , (∧-cons (⟲ (𝕤 𝕫)) (x+𝕤𝕫≡𝕤x x))))


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

𝕤x>𝕫 : (x : ℕ) → (𝕤 x) > 𝕫
𝕤x>𝕫 𝕫 = 𝕤𝕫>𝕫
𝕤x>𝕫 (𝕤 n) = [𝕤x>𝕫]→[𝕤𝕤x>𝕫] n (𝕤x>𝕫 n)



even : ℕ → 𝔹
even 𝕫 = 𝕥
even (𝕤 𝕫) = 𝕗
even (𝕤 (𝕤 n)) = even n

odd : ℕ → 𝔹
odd 𝕫 = 𝕗
odd (𝕤 𝕫) = 𝕥
odd (𝕤 (𝕤 n)) = odd n

Even1 : ℕ → ★₀
Even1 n = (even n) ≡ 𝕥

Odd1 : ℕ → ★₀
Odd1 n = (odd n) ≡ 𝕥

𝕫-Even1 : Even1 𝕫
𝕫-Even1 = ⟲ 𝕥

![𝕫-Odd1] : odd 𝕫 ≡ 𝕗
![𝕫-Odd1] = ⟲ 𝕗

[even-𝕫≡𝕥]→[even-𝕤𝕫≡𝕗] : (even 𝕫) ≡ 𝕥 → (even (𝕤 𝕫)) ≡ 𝕗
[even-𝕫≡𝕥]→[even-𝕤𝕫≡𝕗] [even-𝕫≡𝕥] = ⟲ 𝕗

even-𝕫≡even-𝕤𝕤𝕫 : (even 𝕫) ≡ even (𝕤 (𝕤 𝕫))
even-𝕫≡even-𝕤𝕤𝕫 = ⟲ 𝕥

[even-n≡even-𝕤𝕤n]→[even-𝕤n≡even-𝕤𝕤𝕤n] : (n : ℕ) → (even n) ≡ (even (𝕤 (𝕤 n))) → (even (𝕤 n)) ≡ (even (𝕤 (𝕤 (𝕤 n))))
[even-n≡even-𝕤𝕤n]→[even-𝕤n≡even-𝕤𝕤𝕤n] n [even-n≡even-𝕤𝕤n] = ⟲ (even (𝕤 n))

even-n≡even-𝕤𝕤n : (n : ℕ) → (even n) ≡ (even (𝕤 (𝕤 n)))
even-n≡even-𝕤𝕤n 𝕫 = even-𝕫≡even-𝕤𝕤𝕫
even-n≡even-𝕤𝕤n (𝕤 n) = [even-n≡even-𝕤𝕤n]→[even-𝕤n≡even-𝕤𝕤𝕤n] n (even-n≡even-𝕤𝕤n n)

even-𝕤𝕫≡𝕗 : (even (𝕤 𝕫)) ≡ 𝕗
even-𝕤𝕫≡𝕗 = ⟲ 𝕗

[even-n≡𝕥]→[even-n≡even-𝕫] : (n : ℕ) → (even n) ≡ 𝕥 → (even n) ≡ (even 𝕫)
[even-n≡𝕥]→[even-n≡even-𝕫] n = id

[even-n≡𝕗]→[even-n≡even-𝕤𝕫] : (n : ℕ) → (even n) ≡ 𝕗 → (even n) ≡ (even (𝕤 𝕫))
[even-n≡𝕗]→[even-n≡even-𝕤𝕫] n = id

[even-𝕫≠even-𝕤𝕫] : (even 𝕫) ≠ (even (𝕤 𝕫))
[even-𝕫≠even-𝕤𝕫] [even-𝕫≡even-𝕤𝕫] = ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [even-𝕫≡even-𝕤𝕫]


[even-x≠even-𝕤x]→[even-𝕤x≠even-𝕤𝕤x] : (x : ℕ) → (even x) ≠ (even (𝕤 x)) → (even (𝕤 x)) ≠ (even (𝕤 (𝕤 x)))
[even-x≠even-𝕤x]→[even-𝕤x≠even-𝕤𝕤x] x [even-x≠even-𝕤x] [even-𝕤x≡even-𝕤𝕤x] = ☢
 where
  [even-𝕤𝕤x≡even-x] : (even (𝕤 (𝕤 x))) ≡ (even x) 
  [even-𝕤𝕤x≡even-x] = ≡-↑↓ (even-n≡even-𝕤𝕤n x)
  
  [even-𝕤x≡even-x] : (even (𝕤 x)) ≡ (even x)
  [even-𝕤x≡even-x] = ≡-⇶ [even-𝕤x≡even-𝕤𝕤x] [even-𝕤𝕤x≡even-x]

  ☢ : ⊥
  ☢ = [even-x≠even-𝕤x] (≡-↑↓ [even-𝕤x≡even-x])
 


[even-x≠even-𝕤x] : (x : ℕ) → (even x) ≠ (even (𝕤 x))
[even-x≠even-𝕤x] 𝕫 = [even-𝕫≠even-𝕤𝕫]
[even-x≠even-𝕤x] (𝕤 x) = [even-x≠even-𝕤x]→[even-𝕤x≠even-𝕤𝕤x] x ([even-x≠even-𝕤x] x)





𝕤𝕫≠𝕫 : (𝕤 𝕫) ≠ 𝕫
𝕤𝕫≠𝕫 [𝕤𝕫≡𝕫] = ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 ([f≡g]→[fa≡ga]₂ even even (⟲ even) 𝕫 (𝕤 𝕫) (≡-↑↓ [𝕤𝕫≡𝕫]))


[𝕤x≠x]→[𝕤𝕤x≠𝕤x] : (x : ℕ) → (𝕤 x) ≠ x → (𝕤 (𝕤 x)) ≠ (𝕤 x)
[𝕤x≠x]→[𝕤𝕤x≠𝕤x] x [𝕤x≠x] [𝕤𝕤x≡𝕤x] = ☢
 where
  ☢ : ⊥
  ☢ = [𝕤x≠x] ([a≡b]→[fa≡fb] pred (𝕤 (𝕤 x)) (𝕤 x) [𝕤𝕤x≡𝕤x])

𝕤x≠x : (x : ℕ) → (𝕤 x) ≠ x
𝕤x≠x 𝕫 = 𝕤𝕫≠𝕫
𝕤x≠x (𝕤 x) = [𝕤x≠x]→[𝕤𝕤x≠𝕤x] x (𝕤x≠x x)

{-
[[even-n≡𝕥]→[even-𝕤n≡𝕗]]→[[even-𝕤n≡𝕥]→[even-𝕤𝕤n≡𝕗]] : 
 (n : ℕat) → ( (even n) ≡ 𝕥  → (even (𝕤 n)) ≡ 𝕗) → even (𝕤 n) ≡ 𝕥 → even (𝕤 (𝕤 n)) ≡ 𝕗
[[even-n≡𝕥]→[even-𝕤n≡𝕗]]→[[even-𝕤n≡𝕥]→[even-𝕤𝕤n≡𝕗]] n [[even-n≡𝕥]→[even-𝕤n≡𝕗]] [even-𝕤n≡𝕥] = [even-𝕤𝕤n≡𝕗]
 where
  [[even-n≡𝕥]→[even-𝕤n≡𝕗]]
  [even-𝕤n≡𝕥]

  

  [even-𝕤𝕤n≡𝕗]
-}
{-
[even-n≡𝕥]→[even-𝕤n≡𝕗] : (n : ℕ) → (even n) ≡ 𝕥 → (even 𝕤n) ≡ 𝕗
[even-n≡𝕥]→[even-𝕤n≡𝕗] n [even-n≡𝕥] =
-}

{-
¬[𝕫-Odd] : ¬ (Odd 𝕫)
¬[𝕫-Odd] = ⟲ ⊥
-}

{-
Even→[¬Odd] : (n : ℕ) → Even n → ¬ (Odd n)
Even→[¬Odd] n [n-Even] = 
-}
_gte_ : ℕ → ℕ → 𝔹
x gte 𝕫 = 𝕥
𝕫 gte (𝕤 n) = 𝕗
(𝕤 n) gte (𝕤 m) = n gte (𝕤 m)
infix 2 _gte_ 

x-gte-𝕫→x≥𝕫 : (x : ℕ) → x gte 𝕫 ≡ 𝕥 → x ≥ 𝕫
x-gte-𝕫→x≥𝕫 x [x-gte-𝕫≡𝕥] = [x≥𝕫]
 where
  [x≥𝕫] : x ≥ 𝕫
  [x≥𝕫] = x≥𝕫 x

x≥𝕫→x-gte-𝕫 : (x : ℕ) → x ≥ 𝕫 → x gte 𝕫 ≡ 𝕥
x≥𝕫→x-gte-𝕫 x (a , [𝕫+a≡x]) = ⟲ 𝕥

x-gte-𝕫 : (x : ℕ) → x gte 𝕫 ≡ 𝕥
x-gte-𝕫 x = x≥𝕫→x-gte-𝕫 x (x≥𝕫 x)

x≥x : (x : ℕ) → x ≥ x
x≥x x = (𝕫 , (x+𝕫≡x x))

x≤y→y≤z→x≤z : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
x≤y→y≤z→x≤z x y z (a , [x+a≡y]) (b , [y+b≡z]) = ((a + b) , [x+[a+b]≡z])
 where
--  [x+a≡y]
--  [y+b≡z]
  
  _⊕_ : ℕ → ℕ → ℕ
  x ⊕ y = y + x
  infix 2 _⊕_

  [[x+a]+b≡y+b] : (x + a) + b ≡ y + b
  [[x+a]+b≡y+b] = [f≡g]→[fa≡ga]₂ (_⊕_ b) (_⊕_ b) (⟲ (_⊕_ b)) (x + a) y [x+a≡y]
 
  [[x+a]+b≡x+[a+b]] : (x + a) + b ≡ x + (a + b)
  [[x+a]+b≡x+[a+b]] = [a+b]+c≡a+[b+c] x a b

  [x+[a+b]≡y+b] : x + (a + b) ≡ y + b
  [x+[a+b]≡y+b] = ≡-⇶ (≡-↑↓ [[x+a]+b≡x+[a+b]]) [[x+a]+b≡y+b]
 

  [x+[a+b]≡z] : x + (a + b) ≡ z
  [x+[a+b]≡z] = ≡-⇶ [x+[a+b]≡y+b] [y+b≡z]

_⊕_ : ℕ → ℕ → ℕ
x ⊕ y = y + x
infix 2 _⊕_


x<y→y<z→x<z : (x y z : ℕ) → x < y → y < z → x < z
x<y→y<z→x<z 
 x y z 
 (a , (a' , (∧-cons [𝕤a'≡a] [x+a≡y]))) 
 (b , (b' ,(∧-cons [𝕤b'≡b] [y+b≡z]))) 

 = ((a + b) , ( (𝕤 (a' + b')) , (∧-cons [𝕤𝕤[a'+b']≡a+b] [x+[a+b]≡z])))
   
 where
-- [𝕤a'≡a]
-- [𝕤b'≡b]
   


   [𝕤a'+b≡a+b] : (𝕤 a') + b ≡ a + b
   [𝕤a'+b≡a+b] = [f≡g]→[fa≡ga]₂ (_⊕_ b) (_⊕_ b) (⟲ (_⊕_ b)) (𝕤 a') a [𝕤a'≡a]
 
   [𝕤a'+b≡𝕤[a'+b]] : (𝕤 a') + b ≡ 𝕤 (a' + b)
   [𝕤a'+b≡𝕤[a'+b]] = 𝕤x+y≡𝕤[x+y] a' b

   [a'+b≡a'+𝕤b'] : a' + b ≡ a' + (𝕤 b')
   [a'+b≡a'+𝕤b'] = [f≡g]→[fa≡ga]₂ (_+_ a') (_+_ a') (⟲ (_+_ a')) b (𝕤 b') (≡-↑↓ [𝕤b'≡b])

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

--   [𝕤a'+𝕤b'≡a+b]   
    
   [𝕤𝕤[a'+b']≡a+b] : (𝕤 (𝕤 (a' + b'))) ≡ a + b
   [𝕤𝕤[a'+b']≡a+b] = ≡-↑↓ (≡-⇶ (≡-↑↓ [𝕤a'+b≡a+b]) [𝕤a'+b≡𝕤𝕤[a'+b']])

-- [x+a≡y]
-- [y+b≡z]

   [[x+a]+b≡y+b] : (x + a) + b ≡ y + b
   [[x+a]+b≡y+b] = [f≡g]→[fa≡ga]₂ (_⊕_ b) (_⊕_ b) (⟲ (_⊕_ b)) (x + a) y [x+a≡y]

   [[x+a]+b≡z] : (x + a) + b ≡ z
   [[x+a]+b≡z] = ≡-⇶ [[x+a]+b≡y+b] [y+b≡z]

   [[x+a]+b≡x+[a+b]] : (x + a) + b ≡ x + (a + b)
   [[x+a]+b≡x+[a+b]] = [a+b]+c≡a+[b+c] x a b
  
   [x+[a+b]≡z] : x + (a + b) ≡ z
   [x+[a+b]≡z] = ≡-⇶ (≡-↑↓ [[x+a]+b≡x+[a+b]]) [[x+a]+b≡z]

{-
𝕤x-gte-x : (x : ℕ) → (𝕤 x) gte x ≡ 𝕥
𝕤x-gte-x x = 
-}


x≥y→𝕤x≥y : (x y : ℕ) → x ≥ y → (𝕤 x) ≥ y
x≥y→𝕤x≥y x y (a , [y+a≡x]) = ((𝕤 a) , [y+𝕤a≡𝕤x])
 where
  --[y+a≡x]
  [𝕤[y+a]≡y+𝕤a] : (𝕤 (y + a)) ≡ y + (𝕤 a)
  [𝕤[y+a]≡y+𝕤a] = 𝕤[x+y]≡x+𝕤y y a

  [𝕤[y+a]≡𝕤x] : (𝕤 (y + a)) ≡ (𝕤 x)
  [𝕤[y+a]≡𝕤x] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) (y + a) x [y+a≡x]

  [y+𝕤a≡𝕤x] : y + (𝕤 a) ≡ (𝕤 x)
  [y+𝕤a≡𝕤x] = ≡-⇶ (≡-↑↓ [𝕤[y+a]≡y+𝕤a]) [𝕤[y+a]≡𝕤x]

{-
[x-gte-y→x≥y]→[𝕤x-gte-y→𝕤x≥y] : (x y : ℕ) → (x gte y ≡ 𝕥 → x ≥ y) → (𝕤 x) gte y ≡ 𝕥 → (𝕤 x) ≥ y
[x-gte-y→x≥y]→[𝕤x-gte-y→𝕤x≥y] x y [[x-gte-y≡𝕥]→[x≥y]] [𝕤x-gte-y≡𝕥] = (a, y + a ≡ (𝕤 x))
 where
  [[x-gte-y≡𝕥]→[x≥y]]
  [𝕤x-gte-y≡𝕥]

  [𝕤x≥y]
-}

{-
[x-gte-y→x≥y] : (x y : ℕ) → x gte y ≡ 𝕥  → x ≥ y
[x-gte-y→x≥y] x y [x-gte-y≡𝕥] =
-}

{-
x≯x : (x : ℕ) → x ≯ x
x≯x x [x>x] = ☢
 where
  
  ☢
-}


𝕫≯𝕫 : 𝕫 ≯ 𝕫
𝕫≯𝕫 (a , (b , (∧-cons [𝕤b≡a] [𝕫+a≡𝕫]))) = ☢
 where
  [𝕫+𝕤b≡𝕫+a] : 𝕫 + (𝕤 b) ≡ 𝕫 + a
  [𝕫+𝕤b≡𝕫+a] = [f≡g]→[fa≡ga]₂ (_+_ 𝕫) (_+_ 𝕫) (⟲ (_+_ 𝕫)) (𝕤 b) a [𝕤b≡a]  

  [𝕫+𝕤b≡𝕫] : 𝕫 + (𝕤 b) ≡ 𝕫
  [𝕫+𝕤b≡𝕫] = ≡-⇶ [𝕫+𝕤b≡𝕫+a] [𝕫+a≡𝕫]

  [𝕫+𝕤b≡𝕤b] : 𝕫 + (𝕤 b) ≡ 𝕤 b
  [𝕫+𝕤b≡𝕤b] = 𝕫+x≡x (𝕤 b)

  [𝕤b≡𝕫] : (𝕤 b) ≡ 𝕫
  [𝕤b≡𝕫] = ≡-⇶ (≡-↑↓ [𝕫+𝕤b≡𝕤b]) [𝕫+𝕤b≡𝕫]

  ☢ : ⊥
  ☢ = 𝕤x≠𝕫 b [𝕤b≡𝕫]

[x+𝕫≡x]→[𝕫≡𝕫] : (x : ℕ) → x + 𝕫 ≡ x → 𝕫 ≡ 𝕫
[x+𝕫≡x]→[𝕫≡𝕫] x [x+𝕫≡x] = ⟲ 𝕫

𝕤x+𝕫≠x : (x : ℕ) → (𝕤 x) + 𝕫 ≠ x
𝕤x+𝕫≠x x [𝕤x+𝕫≡x] = ☢
 where
  [𝕤x+𝕫≡𝕤x] : (𝕤 x) + 𝕫 ≡ (𝕤 x)
  [𝕤x+𝕫≡𝕤x] = x+𝕫≡x (𝕤 x)

  [𝕤x≡x] : (𝕤 x) ≡ x
  [𝕤x≡x] = ≡-⇶ (≡-↑↓ [𝕤x+𝕫≡𝕤x]) [𝕤x+𝕫≡x]

  ☢ : ⊥
  ☢ = 𝕤x≠x x [𝕤x≡x]

{-
[𝕤x+y≠x]→[𝕤x+𝕤y≠x] : (x y : ℕ) → (𝕤 x) + y ≠ x → (𝕤 x) + (𝕤 y) ≠ x
[𝕤x+y≠x]→[𝕤x+𝕤y≠x] x y [𝕤x+y≠x] [𝕤x+𝕤y≡x] = ☢
 where
  
  ☢
-}

{-
𝕤x+y≠x : (x y : ℕ) → (𝕤 x) + y ≠ x
𝕤x+y≠x x [𝕤x+y≡x] = ☢
 where
  
  ☢
-}
x+𝕤𝕫≠x : (x : ℕ) → x + (𝕤 𝕫) ≠ x
x+𝕤𝕫≠x x [x+𝕤𝕫≡x] = ☢
 where
  [x+𝕤𝕫≡𝕤x] : x + (𝕤 𝕫) ≡ (𝕤 x)
  [x+𝕤𝕫≡𝕤x] = x+𝕤𝕫≡𝕤x x

  [𝕤x≡x] : (𝕤 x) ≡ x
  [𝕤x≡x] = ≡-⇶ (≡-↑↓ [x+𝕤𝕫≡𝕤x]) [x+𝕤𝕫≡x]

  ☢ : ⊥
  ☢ = 𝕤x≠x x [𝕤x≡x]


{-
[x+𝕤y≠x]→[x+𝕤𝕤y≠x] : (x y : ℕ) → x + (𝕤 y) ≠ x → x + (𝕤 (𝕤 y)) ≠ x
[x+𝕤y≠x]→[x+𝕤𝕤y≠x] x y [x+𝕤y≠x] [x+𝕤𝕤y≡x] = ☢
 where
  
  ☢
-}
{-
x+𝕤y≠x : (x y : ℕ) → x + (𝕤 y) ≠ x
x+𝕤y≠x x y [x+𝕤y≡x] = ☢
 where
  [𝕤[x+y]≡x+𝕤y] : (𝕤 (x + y)) ≡ x + (𝕤 y)
  [𝕤[x+y]≡x+𝕤y] = 𝕤[x+y]≡x+𝕤y x y
  
  [𝕤[x+y]≡x] : (𝕤 (x + y)) ≡ x
  [𝕤[x+y]≡x] = ≡-⇶ [𝕤[x+y]≡x+𝕤y] [x+𝕤y≡x]

  ☢
-}
{-
[[x+y≡x]→[y≡𝕫]]→[[x+𝕤y≡x]→[𝕤y≡𝕫]] : (x y : ℕ) → (x + y ≡ x → y ≡ 𝕫) → x + (𝕤 y) ≡ x → (𝕤 y) ≡ 𝕫
[[x+y≡x]→[y≡𝕫]]→[[x+𝕤y≡x]→[𝕤y≡𝕫]] x y [[x+y≡x]→[y≡𝕫]] [x+𝕤y≡x] = [𝕤y≡𝕫]
 where
  [𝕤[x+y]≡x+𝕤y] : (𝕤 (x + y)) ≡ x + (𝕤 y)
  [𝕤[x+y]≡x+𝕤y] = 𝕤[x+y]≡x+𝕤y x y

  [𝕤[x+y]≡x] : (𝕤 (x + y)) ≡ x
  [𝕤[x+y]≡x] = ≡-⇶ [𝕤[x+y]≡x+𝕤y] [x+𝕤y≡x]

  [𝕤[x+y]≡𝕤x+y] : (𝕤 (x + y)) ≡ (𝕤 x) + y
  [𝕤[x+y]≡𝕤x+y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x y)

  {-
  [𝕤[x+y]≡𝕤x] : (𝕤 (x + y)) ≡ 𝕤 x
  [𝕤[x+y]≡𝕤x] = 
  [x+𝕤y≡x]
  -} 
  [𝕤y≡𝕫]
-}
{-
[x+y≡x]→[y≡𝕫] : (x y : ℕ) → x + y ≡ x → y ≡ 𝕫
[x+y≡x]→[y≡𝕫] x y [x+y≡x] = [y≡𝕫]
 where
  
  [y≡𝕫]
-}

{-
[x≯x]→[𝕤x≯𝕤x] : (x : ℕ) → x ≯ x → (𝕤 x) ≯ (𝕤 x)
[x≯x]→[𝕤x≯𝕤x] x [x≯x] (a , (b , (∧-cons [𝕤b≡a] [𝕤x+a≡𝕤x] = ☢
 where
  ☢
-}

{-
[𝕫>𝕫]→[𝕫≠𝕫] 
[[x>𝕫]→[x≠𝕫]]→[[𝕤x>𝕫]→[𝕤x≠𝕫]] : (x : ℕ) → (x > 𝕫 → x ≠ 𝕫) → (𝕤 x) > 𝕫 → (𝕤 x) ≠ 𝕫
[[x>𝕫]→[x≠𝕫]]→[[𝕤x>𝕫]→[𝕤x≠𝕫]] x [x>𝕫→x≠𝕫] [𝕤x>𝕫] [𝕤x≡𝕫] = ☢
 where
  ☢
[x>𝕫]→[x≠𝕫] : (x : ℕ) → x > 𝕫 → x ≠ 𝕫
[x>𝕫]→[x≠𝕫] x (a , (b , (∧-cons [𝕤b≡a] [𝕫+b≡x]))) = [[x>𝕫]→[x≠𝕫]]
 where
  
  [[x>𝕫]→[x≠𝕫]]
-}
{-
[x>y]→[x≠y] : (x : ℕ)  → (y : ℕ) → x > y → x ≠ y
[x>y]→[x≠y] x y (a , (b , (∧-cons [𝕤a≡b] [x+b≡y]))) = [x≠y]
-}


{-
_minus₀ : ℕ → ℕ → ℕ
-}


-- multiplication on Nats
_*_ : ℕ → ℕ → ℕ
𝕫 * y = 𝕫 
(𝕤 x) * y = y + (x * y) 
infixr 2 _*_


𝕫*x≡𝕫 : (x : ℕ) → 𝕫 * x ≡ 𝕫
𝕫*x≡𝕫 x = ⟲ 𝕫

𝕤𝕫*x≡x : (x : ℕ) → (𝕤 𝕫) * x ≡ x
𝕤𝕫*x≡x x = [𝕤𝕫*x≡x] 
 where
  [𝕤𝕫*x≡x+[𝕫*x]] : (𝕤 𝕫) * x ≡ x + (𝕫 * x)
  [𝕤𝕫*x≡x+[𝕫*x]] = ⟲ (x + (𝕫 * x))

  [x+[𝕫*x]≡x+𝕫] : x + (𝕫 * x) ≡ x + 𝕫
  [x+[𝕫*x]≡x+𝕫] = [f≡g]→[fa≡ga]₂ (_+_ x) (_+_ x) (⟲ (_+_ x)) (𝕫 * x) 𝕫 (𝕫*x≡𝕫 x)

  [x+𝕫≡x] : (x + 𝕫) ≡ x
  [x+𝕫≡x] = x+𝕫≡x x

  [𝕤𝕫*x≡x+𝕫] : (𝕤 𝕫) * x ≡ x + 𝕫
  [𝕤𝕫*x≡x+𝕫] = ≡-⇶ [𝕤𝕫*x≡x+[𝕫*x]] [x+[𝕫*x]≡x+𝕫]
 
  [𝕤𝕫*x≡x] : (𝕤 𝕫) * x ≡ x
  [𝕤𝕫*x≡x] = ≡-⇶ [𝕤𝕫*x≡x+𝕫] [x+𝕫≡x]


diff : ℕ → ℕ → ℕ
diff 𝕫 x = x
diff x 𝕫 = x
diff (𝕤 x) (𝕤 y) = diff x y

diff-𝕫-𝕫≡𝕫 : diff 𝕫 𝕫 ≡ 𝕫
diff-𝕫-𝕫≡𝕫 = ⟲ 𝕫

[diff-x-x≡𝕫]→[diff-𝕤x-𝕤x≡𝕫] : (x : ℕ) → diff x x ≡ 𝕫 → diff (𝕤 x) (𝕤 x) ≡ 𝕫
[diff-x-x≡𝕫]→[diff-𝕤x-𝕤x≡𝕫] x [diff-x-x≡𝕫] = [diff-𝕤x-𝕤x≡𝕫]
 where
  [diff-𝕤x-𝕤x≡diff-x-x] : diff (𝕤 x) (𝕤 x) ≡ diff x x
  [diff-𝕤x-𝕤x≡diff-x-x] = ⟲ (diff x x)

  [diff-𝕤x-𝕤x≡𝕫] :  diff (𝕤 x) (𝕤 x) ≡ 𝕫
  [diff-𝕤x-𝕤x≡𝕫] = ≡-⇶ [diff-𝕤x-𝕤x≡diff-x-x] [diff-x-x≡𝕫]


diff-x-x≡𝕫 : (x : ℕ) → diff x x ≡ 𝕫
diff-x-x≡𝕫 𝕫 = diff-𝕫-𝕫≡𝕫
diff-x-x≡𝕫 (𝕤 x) = [diff-x-x≡𝕫]→[diff-𝕤x-𝕤x≡𝕫] x (diff-x-x≡𝕫 x)

diff-𝕫-𝕫≡diff-𝕫-𝕫 : diff 𝕫 𝕫 ≡ diff 𝕫 𝕫
diff-𝕫-𝕫≡diff-𝕫-𝕫 = ⟲ (diff 𝕫 𝕫)

diff-𝕤x-𝕤y≡diff-x-y : (x y : ℕ) → diff (𝕤 x) (𝕤 y) ≡ diff x y
diff-𝕤x-𝕤y≡diff-x-y x y = ⟲ (diff x y)


diff-𝕫-x≡x : (x : ℕ) → diff 𝕫 x ≡ x
diff-𝕫-x≡x x = ⟲ x

diff-𝕤x-𝕫≡𝕤x : (x : ℕ) → diff (𝕤 x) 𝕫 ≡ (𝕤 x)
diff-𝕤x-𝕫≡𝕤x x = ⟲ (𝕤 x)


[diff-x-𝕫≡x]→[diff-𝕤x-𝕫≡𝕤x] : (x : ℕ) → diff x 𝕫 ≡ x → diff (𝕤 x) 𝕫 ≡ (𝕤 x)
[diff-x-𝕫≡x]→[diff-𝕤x-𝕫≡𝕤x] x [diff-x-𝕫≡x] = diff-𝕤x-𝕫≡𝕤x x


diff-x-𝕫≡x : (x : ℕ) → diff x 𝕫 ≡ x
diff-x-𝕫≡x 𝕫 = diff-𝕫-𝕫≡𝕫
diff-x-𝕫≡x (𝕤 x) = [diff-x-𝕫≡x]→[diff-𝕤x-𝕫≡𝕤x] x (diff-x-𝕫≡x x)


diff-x-𝕫≡diff-𝕫-x : (x : ℕ) → diff x 𝕫 ≡ diff 𝕫 x
diff-x-𝕫≡diff-𝕫-x x = ≡-⇶ (diff-x-𝕫≡x x) (≡-↑↓ (diff-𝕫-x≡x x))

[diff-𝕫-𝕫≡𝕫]→[diff-𝕤𝕫-𝕫≡𝕤𝕫] : diff 𝕫 𝕫 ≡ 𝕫 → diff (𝕤 𝕫) 𝕫 ≡ (𝕤 𝕫)
[diff-𝕫-𝕫≡𝕫]→[diff-𝕤𝕫-𝕫≡𝕤𝕫] [diff-𝕫-𝕫≡𝕫] = diff-𝕤x-𝕫≡𝕤x 𝕫

{-
[diff-x-𝕫≡𝕫]→[diff-𝕤x-𝕫≡𝕤𝕫] : (x : ℕ) → diff x 𝕫 ≡ 𝕫 → diff (𝕤 x) 𝕫 ≡ (𝕤 𝕫)
[diff-x-𝕫≡𝕫]→[diff-𝕤x-𝕫≡𝕤𝕫] x [diff-x-𝕫≡𝕫] = 
-}

[diff-𝕫-𝕫≡𝕫]→[𝕫≡𝕫] : diff 𝕫 𝕫 ≡ 𝕫 → 𝕫 ≡ 𝕫
[diff-𝕫-𝕫≡𝕫]→[𝕫≡𝕫] [diff-𝕫-𝕫≡𝕫] = ⟲ 𝕫

[[diff-x-y≡𝕫]→[x≡y]]→[[diff-𝕤x-𝕤y≡𝕫]→[𝕤x≡𝕤y]] : (x y : ℕ) → (diff x y ≡ 𝕫 → x ≡ y) → diff (𝕤 x) (𝕤 y) ≡ 𝕫 → (𝕤 x) ≡ (𝕤 y)
[[diff-x-y≡𝕫]→[x≡y]]→[[diff-𝕤x-𝕤y≡𝕫]→[𝕤x≡𝕤y]] x y [[diff-x-y≡𝕫]→[x≡y]] [diff-𝕤x-𝕤y≡𝕫] = [𝕤x≡𝕤y]
 where
  [diff-𝕤x-𝕤y≡diff-x-y] : diff (𝕤 x) (𝕤 y) ≡ diff x y
  [diff-𝕤x-𝕤y≡diff-x-y] = diff-𝕤x-𝕤y≡diff-x-y x y

  [diff-x-y≡𝕫] : diff x y ≡ 𝕫
  [diff-x-y≡𝕫] = ≡-⇶ (≡-↑↓ [diff-𝕤x-𝕤y≡diff-x-y]) [diff-𝕤x-𝕤y≡𝕫]

  [x≡y] : x ≡ y
  [x≡y] = [[diff-x-y≡𝕫]→[x≡y]] [diff-x-y≡𝕫]

  [𝕤x≡𝕤y] : (𝕤 x) ≡ (𝕤 y)
  [𝕤x≡𝕤y] = [f≡g]→[fa≡ga]₂ 𝕤 𝕤 (⟲ 𝕤) x y [x≡y]

{-
𝕤x≠𝕫 : (x : ℕ) → (𝕤 x) ≠ 𝕫
𝕤x≠𝕫 x [𝕤x≡𝕫] = ☢
 where
-}

diff-𝕤𝕫-𝕫≠𝕫 : diff (𝕤 𝕫) 𝕫 ≠ 𝕫
diff-𝕤𝕫-𝕫≠𝕫 [diff-𝕤𝕫-𝕫≡𝕫] = ☢
 where
  [diff-𝕤𝕫-𝕫≡𝕤𝕫] : diff (𝕤 𝕫) 𝕫 ≡ (𝕤 𝕫)
  [diff-𝕤𝕫-𝕫≡𝕤𝕫] = diff-𝕤x-𝕫≡𝕤x 𝕫

  [𝕤𝕫≡𝕫] : (𝕤 𝕫) ≡ 𝕫
  [𝕤𝕫≡𝕫] = ≡-⇶ (≡-↑↓ [diff-𝕤𝕫-𝕫≡𝕤𝕫]) [diff-𝕤𝕫-𝕫≡𝕫]

  ☢ : ⊥
  ☢ = 𝕤𝕫≠𝕫 [𝕤𝕫≡𝕫]
{-
[diff-𝕤x-𝕫≠𝕫]→[diff-𝕤𝕤x-𝕫≠𝕫] : (x : ℕ) → diff (𝕤 x) 𝕫 ≠ 𝕫 → diff (𝕤 (𝕤 x)) 𝕫 ≠ 𝕫
[diff-𝕤x-𝕫≠𝕫]→[diff-𝕤𝕤x-𝕫≠𝕫] x [diff-𝕤x-𝕫≠𝕫] [diff-𝕤𝕤x-𝕫≡𝕫] = ☢
 where
  
  ☢
-}
{-
diff-𝕤x-𝕫≠𝕫 : (x : ℕ) → diff (𝕤 x) 𝕫 ≠ 𝕫
diff-𝕤x-𝕫≠𝕫 x [diff-𝕤x-𝕫≡𝕫] = ☢
 where
  [diff-𝕤x-𝕫≡𝕤x] : diff (𝕤 x) 𝕫 ≡ (𝕤 x)
  [diff-𝕤x-𝕫≡𝕤x] = diff-x-𝕫≡x (𝕤 x)

  [𝕤x≡𝕫] : (𝕤 x) ≡ 𝕫
  [𝕤x≡𝕫] = ≡-⇶ (≡-↑↓ [diff-𝕤x-𝕫≡𝕤x]) [diff-𝕤x-𝕫≡𝕫]

  ☢
-}
{-
[diff-x-y≡𝕫]→[x≡y] : (x y : ℕ) → diff x y ≡ 𝕫 → x ≡ y
[diff-x-y≡𝕫]→[x≡y] 𝕫 𝕫 [diff-𝕫-𝕫≡𝕫] = ⟲ 𝕫
[diff-x-y≡𝕫]→[x≡y] (𝕤 x) 𝕫 [diff-𝕤x-𝕫≡𝕫]
[diff-x-y≡𝕫]→[x≡y] (𝕤 x) (𝕤 y) [diff-x-y≡𝕫] = [[diff-x-y≡𝕫]→[x≡y]]→[[diff-𝕤x-𝕤y≡𝕫]→[𝕤x≡𝕤y]] x y ([diff-x-y≡𝕫]→[x≡y] x y)
-}

{-
[diff-x-y≡𝕫]→[diff-𝕤x-y≡𝕤𝕫] : (x y : ℕ) → diff x y ≡ 𝕫 → diff (𝕤 x) y ≡ (𝕤 𝕫)
[diff-x-y≡𝕫]→[diff-𝕤x-y≡𝕤𝕫] x y [diff-x-y≡𝕫] = [diff-𝕤x-y≡𝕤z]
-}

{-
[diff-x-y≡diff-y-x]→[diff-x-𝕤y≡diff-𝕤y-x] : (x y : ℕ) → diff x y ≡ diff y x → diff x (𝕤 y) ≡ diff (𝕤 y) x
[diff-x-y≡diff-y-x]→[diff-x-𝕤y≡diff-𝕤y-x] x y [diff-x-y≡diff-y-x] = [diff-x-𝕤y≡diff-𝕤y-x]
 where
  
  [diff-x-𝕤y≡diff-𝕤y-x]
-}

{-
diff-x-y≡diff-y-x
-}
{-
[≡0%n] 
data Even (n : ℕ) : ★₀ where
-}

{-
+-assoc : is-associative +
+-assoc x y z = ... : (x + y) + z ≡ x + (y + z)
-}

{-
zero-id : is-identity add zero
zero-id a = 
 record {
  andFst = refl a;
  andSnd = refl a
 }
-}
{-
zero-id : is-identity add2 zero
zero-id a =
 record {
  andFst = refl a;
  andSnd = refl a
 }
-}
{-
add-id : has-identity add
add-id = 
 record {
  proj1 = zero;
  proj2 = zero-id add zero
 }
  -}


{-
  We already know this should work because of functions_repect_identity, but let's
  just make sure it applies to constructors:
-}
[a≡b]→[𝕤a≡𝕤b] : (a b : ℕ) → a ≡ b → 𝕤 a ≡ 𝕤 b
[a≡b]→[𝕤a≡𝕤b] a b [a≡b] = [a≡b]→[fa≡fb] 𝕤 a b [a≡b]




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


fib-unfib-is-id : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → (a : A) → a ≡ (unfibrate f (fibrate f a))
fib-unfib-is-id {α} {β} {A} {B} f a = ⟲ a


fib-unfib-is-id-strong : ∀ {α β} {A : ★ α} {B : ★ β} → (f : A → B) → id ≡ ((unfibrate f) ∘ (fibrate f))
fib-unfib-is-id-strong {α} {β} {A} {B} f = ⟲ (λ a → a)

injection : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
injection {α} {β} {A} {B} f = (a1 a2 : A) → (f a1 ≡ f a2) → (a1 ≡ a2)

surjection : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
surjection {α} {β} {A} {B} f = (b : B) → fiber f b 


bijection : ∀ {α β} {A : ★ α} {B : ★ β} (f : A → B) → ★ (α ⊔ β)
bijection {α} {β} {A} {B} f = (injection f) ∧ (surjection f) 


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


-- extensional equality of functions
FuncId : ∀ {α β} {A : ★ α} {B : ★ β} (f g : A → B) → ★ (α ⊔ β)
FuncId {α} {β} {A} {B} f g = (a : A) → f a ≡ g a


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

{-
record iso-strong {m n : Level} (A : Set m) (B : Set n) : Set (lmax m n) where
 field
  isoA : A -> B
  isoB : B -> A
  left : left-inv-strong isoB isoA
  right : right-inv-strong isoB isoA
-} 


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
 


--functions from False to True are injections 
F-T-is-injection : (f : ⊥ → ⊤) → injection f
F-T-is-injection f a1 a2 [fa1≡fa2] = ω a1

--functions from False to True are not surjections
F-T-not-surjection : (f : ⊥ → ⊤) → surjection f → ⊥
F-T-not-surjection f surj = π₁ (surj ●)


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


-- two sets are related by injectivity if there is an injection between them
injective : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
injective {α} {β} A B = ∃ f ∈ (A -> B) , (injection f)

-- etc..
surjective : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
surjective {m} {n} A B = ∃ f ∈ (A -> B) , (surjection f)


bijective : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
bijective {α} {β} A B = (injective A B) ∧ (surjective A B)


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



-- needs more defining axioms in order to actually characterizie it as a Functor
record Functor {α β} {A : ★ α} {B : ★ β} : ★ (α ⊔ β) where
 field
  omap : A → B
  fmap : (A → A) → (B → B)
  
  

data [_] {α} (A : ★ α) : ★ α where
 [] : [ A ]
 _::_ : A → [ A ] → [ A ]


curry : ∀ {α β γ} {A : ★ α} {B : A → ★ β} {C : ( ∃ a ∈ A , (B a)) → ★ γ} → 
        ((p : ∃ a ∈ A , (B a)) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)



uncurry : 
 ∀ {α β γ} {A : ★ α} {B : A → ★ β} {C : ★ γ} → ((a : A) → (B a) → C) → (∃ a ∈ A , (B a)) → C
uncurry f (x , y) = f x y


true-iso : ∀ {α β} (A : ★ α) (B : ★ β) → ★ (α ⊔ β)
true-iso {α} {β} A B = ∃ f ∈ (A → B) , (∃ g ∈ (B → A) , ((g ∘ f ≡ id) ∧ (f ∘ g ≡ id)))

[f1≡f2]→[g∘f1≡g∘f2] :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} (f1 f2 : A → B) → f1 ≡ f2 → (g : B → C) → (g ∘ f1 ≡ g ∘ f2)
[f1≡f2]→[g∘f1≡g∘f2] {α} {β} {γ} {A} {B} {C} f1 f2 [f1≡f2] g = [g∘f1≡g∘f2]
 where
  g∘ : (A → B) → (A → C)
  g∘ f = g ∘ f 

  [g∘f1≡g∘f2] : g ∘ f1 ≡ g ∘ f2
  [g∘f1≡g∘f2] = [f≡g]→[fa≡ga]₂ g∘ g∘ (⟲ g∘) f1 f2 [f1≡f2]


∘' :
 ∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ} 
 (f : A → B) → (g : B → C) → A → C
∘' f g = g ∘ f


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
[n≠𝕤n] : (n : ℕ) → n ≡ 𝕤 n → ⊥
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
