module Fin12 where

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data Fin : Nat → Set where
 Fin-zero : Fin (suc zero)
 Fin-suc : {n : Nat} → Fin n → Fin (suc n)

data Fin' : Nat → Set where
 Fin'-zero : Fin' 12
 Fin'-suc : {n : Nat} → Fin' n → Fin' (suc n)

