module Int2 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

-- given i, return i + 1.
isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

-- given i, return i - 1.
ipred : Int → Int
ipred (+ (suc n)) = + n
ipred (+ zero) = - (suc zero)
ipred (- n) = - (suc n) 

-- given i, return -i.
ineg : Int → Int
ineg (+ x) = - x
ineg (- x) = + x

-- given i & j, return i + j.
-- have to account for each case of zero & recursively solve with suc as the input
-- for the + and - flips at the bottom. The recursion is a mock way to see which one
-- has a greater absolute value & thus which way the sign should go
iplus : Int → Int → Int
iplus (+ i) (+ j) = + (plus i j)
iplus (- i) (- j) = - (plus i j)
iplus (- zero) (+ j) = + j
iplus (+ zero) (- j) = - j
iplus (- i) (+ zero) = - i
iplus (+ i) (- zero) = + i
iplus (+ (suc i)) (- (suc j)) = iplus (+ i) (- j)
iplus (- (suc i)) (+ (suc j)) = iplus (- i) (+ j)

-- given i & j, return i - j.
iminus : Int → Int → Int
iminus (- i) (+ j)= - (plus i j)
iminus (+ i) (- j) = + (plus i j)
iminus (+ zero) (+ j) = - j
iminus (- zero) (- j) = + j
iminus (- i) (- zero) = - i
iminus (+ i) (+ zero) = + i
iminus (+ (suc i)) (+ (suc j)) = iminus (+ i) (+ j)
iminus (- (suc i)) (- (suc j)) = iminus (- i) (- j)
-- for the one above, I followed the pattern of the iplus, just keeping track of which one was positive & negative due to subtraction.

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (+ i) (+ j) = + (times i j)
itimes (- i) (- j) = + (times i j)
itimes (- zero) (+ n) = - zero
itimes (+ zero) (- n) = - zero
itimes (+ n) (- zero) = - zero
itimes (- n) (+ zero) = - zero
itimes (- i) (+ j) = - (times i j)
itimes (+ i) (- j) = - (times i j)

-- I am not fully sure whether there are more necessary cases for zero. It
-- said that there were unreachable zero cases when I tried the other 2
