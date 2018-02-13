module conjunction-eta where

data Pair (A : Set) (B : Set) : Set where
 _,_ : A -> B -> Pair A B

data Id {A : Set} (x : A) : A -> Set where
 refl : Id x x

fst : {A B : Set} -> Pair A B -> A
fst (a , b) = a

snd : {A B : Set} -> Pair A B -> B
snd (a , b) = b

pair-eta : {A B : Set} -> (p : Pair A B) -> Id p (fst p , snd p)
pair-eta (a , b) = refl
