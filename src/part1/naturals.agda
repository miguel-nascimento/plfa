module part1.naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
  
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(succ m) + n = succ (m + n)
{-# BUILTIN NATPLUS _+_ #-}

infixl 6  _+_

+-example : 3 + 4 ≡ 7
+-example = 
  begin
    3 + 4
  ≡⟨⟩
    succ (2 + 4)
  ≡⟨⟩
    succ (succ (1 + 4))
  ≡⟨⟩
    succ (succ (succ (0 + 4)))
  ≡⟨⟩
    succ (succ (succ 4))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * _ = zero
(succ m) * n = n + (m * n)
{-# BUILTIN NATTIMES _*_ #-}

infixl 7  _*_

*-example : 3 * 4 ≡ 12
*-example =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4) 
  ≡⟨⟩
    4 + 4 + (1 * 4)
  ≡⟨⟩
    4 + 4 + 4 + (0 * 4)
  ≡⟨⟩
    12
  ∎


_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (succ n) = m * (m ^ n)

^-example : 3 ^ 4 ≡ 81
^-example = 
  begin
    3 ^ 4
  ≡⟨⟩
    (3 ^ 3) * (3 ^ 1) * (3 ^ 0)
  ≡⟨⟩
    (3 ^ 2) * (3 ^ 1) * (3 ^ 1) * (3 ^ 0)
  ≡⟨⟩
    (3 ^ 1) * (3 ^ 1) * (3 ^ 1) * (3 ^ 1) * (3 ^ 0)
  ≡⟨⟩
    81
  ∎
     

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ _ = zero
succ m ∸ succ n = m ∸ n
{-# BUILTIN NATMINUS _∸_ #-}

infixl 6  _∸_

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

∸-example₂ : 3 ∸ 5 ≡ 0
∸-example₂ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 3
  ≡⟨⟩
    0
  ∎

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (bin O) = bin I
inc (bin I) = (inc bin) O

_ : inc (⟨⟩ I O I) ≡ ⟨⟩ I I O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (succ n) = inc (to n)

_ : to 3 ≡ ⟨⟩ I I
_ = refl
      
from : Bin → ℕ
from ⟨⟩ = 0 
from (bin O) = 2 * from bin   
from (bin I) = 2 * (from bin) + 1 

_ : from (⟨⟩ I I) ≡ 3
_ = refl