module Quotient

import Data.Nat
import Data.Nat.Division
import Data.Nat.Equational
import Data.Fin
import Data.Nat.Order.Properties
%default total
N,M,D:Nat
N=16
M=4
D=3





-- use elemSmallerThanBound
res1,res2:LT 1 3
res1 = boundModNatNZ 13 3  SIsNonZero

pr1: 1 `lt` 3 = true
res2 = ltIsLT 1 3 pr1

DivisionTheorem' : (numer, denom : Nat) -> (0 prf1 : NonZero denom)
               -> numer = (modNatNZ numer denom prf1) + (divNatNZ numer denom prf1)*denom
DivisionTheorem' numer denom prf1   = rewrite sym $ fstDivmodNatNZeqDiv numer denom prf1 prf1 in
                                      rewrite sym $ sndDivmodNatNZeqMod numer denom prf1 prf1 in
                                      DivisionTheoremDivMod numer denom prf1 


prfDT:13 = 1+M*D
prfDT = DivisionTheorem' 13 3   SIsNonZero 

is3lt4: lt 3 4 =True
is3lt4 = Refl


--  ltReflectsLT 3 4 is3lt4 


orderingSum : (n:Nat) ->  lte  Z     n  = True
orderingSum _   = Refl


z_lte_n : (n:Nat)  -> LTE  Z  n
z_lte_n n =  let p1 : (lte Z n = True)
                 p1 = Refl
             in
             lteReflectsLTE Z n p1 

-- plusZeroRightNeutral : (left : Nat) -> left + Z = left
-- plusLteLeft : (a : Nat) -> LTE b c -> LTE (a + b) (a + c)
sumOrdering : (a,b,c :Nat) -> (prf: a = b + c)-> LTE  (b+Z) (b+c)
sumOrdering a b c prf = let zprf: LTE Z c
                            zprf = z_lte_n c
                            bzero :b + Z = b
                            bzero = plusZeroRightNeutral b
                            lteexp : LTE  (b+Z) (b+c)
                            lteexp = plusLteLeft b zprf
                            --result: LTE b a
                            --result = plusLteLeft ?b1 ?zprf1 
                        in
                        lteexp --plusLteLeft b zprf

-- what is in the left side of equation will become the goal of rewrite
-- e.g `a = b +c `, the term `a` is on the left side will appear in the goal type
-- or in other words what is on the right side of equation `b+c` will be replaced 
-- compound of rewrite evaluate the goal from left to right, first rewrite the `b+0` then `b+c`

sumRewrite: (a,b,c : Nat) -> ( b + c = a )   ->  LTE  (b+0) (b + c ) -> LTE b  a
sumRewrite a b c prf tgt = rewrite sym $ plusZeroRightNeutral b  in 
                              rewrite sym $ prf  in tgt




sumOrder: (a,b,c : Nat) -> ( b + c = a )   ->   LTE b  a
sumOrder a b c prf = let zprf: LTE Z c
                         zprf = z_lte_n c
                         bzero :b + Z = b
                         bzero = plusZeroRightNeutral b
                         lteexp : LTE  (b+Z) (b+c)
                         lteexp = plusLteLeft b zprf
                     in
                     sumRewrite a b c prf lteexp 

p1: Nat -> Type
p1 n = (n=2)

testReplace: (x=y) -> (p1 x) -> (p1 y)
--testReplace a b = replace a ?b1


n3,n4:Nat
n3 = 2
n4 = 4
eqXY:  2 + 2   = 4
eqXY = Refl

testRewrite2: (x=y) -> (p1 y) -> (p1 x)
testRewrite2 a b = rewrite a in b



--quotMultDenom: (numer, denom : Nat) -> (0 prf1 : NonZero denom) -> (divNatNZ numer denom prf1)*denom `lt`  numer = True
--quotMultDenom numer denom prf1 = let divTheorem : DivisionTheorem numer denom SIsNonZero SIsNonZero
--                                     rest1: Nat 
