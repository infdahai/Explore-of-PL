
module agda_test.naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data  ℕ  :  Set where
    zero : ℕ
    suc  : ℕ  → ℕ

{-# BUILTIN NATURAL ℕ  #-}


_+_ : ℕ → ℕ → ℕ
zero  + n  =  n
suc m + n  =  suc (m + n)

_ : 2 + 3 ≡ 5
_ = refl


_*_ : ℕ  →  ℕ →  ℕ
zero * n  = zero
suc m * n  = n + ( m * n)

_ : 5 * 5 ≡ 25
_ = refl

_^_ : ℕ →  ℕ →  ℕ
n ^ (suc m) = n * (n ^ m)
n ^ zero = 1

_ : 3 ^ 4 ≡  81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ : zero ∸ zero ≡ zero
_ = refl

infixl 6 _+_ _∸_
infixl 7 _*_


{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin  : Set  where
    nil : Bin
    x0_ : Bin →  Bin
    x1_ : Bin →  Bin
