module Main where

import qualified All
import qualified PrelGHC
import qualified System

unsafeCoerce = PrelGHC.unsafeCoerce#


i2n :: Integer -> All.Nat
i2n x =  acc All.O x 
 where  
 acc p 0 = p
 acc p n = acc (All.S p) (n-1)

n2i :: All.Nat -> Integer
n2i x = acc 0 x
 where
 acc p All.O = p
 acc p (All.S n) = acc (p+1) n

p2b :: All.Positive -> Integer
p2b All.XH = 1 
p2b (All.XO p) = 2 * (p2b p)
p2b (All.XI p) = 1 + (2 * (p2b p))

z2b :: All.Z -> Integer
z2b All.Z0 = 0
z2b (All.Zpos p) = p2b p
z2b (All.Zneg p) = - (p2b p)

tests = [
  ("one_R", ("One in reals", \_ -> All.one_R)),
  ("one_C", ("One in complex", \_ -> All.c_Re_observer All.one_C)),
  ("half", ("1/2 in reals", \_ -> All.half0 All.Tt)),
  ("sqrt2_old", ("sqrt(2), direct computation", \_ -> All.sqrt_two All.Tt)),
  ("sixteen", ("(x+1)^4 at x=1", \_ -> All.sixteen_R All.Tt)),
  ("e", ("exp(1), by series", \_ -> All.e)),
  ("e_2", ("exp(1), by series, using Z", \_ -> All.e_2)),
  ("e_3", ("exp(1), by series, using Z, linear version of pos_fact_ap_zero", \_ -> All.e_3)),
  ("e_4", ("exp(1), by series, using Z, pos_fact_ap_zero in the model", \_ -> All.e_4)),
  ("new_e", ("exp(1), by series, using directly Q", \_ -> All.new_E)),
--  ("Pi", ("Pi, first version", \_ -> All.pi)),
--  ("pi", ("Pi, second version",  \_ -> All.pi0)),
  ("one_fta", ("One as root of x-1", \_ -> All.c_Re_observer (All.one_fta All.Tt))),
  ("sqrt2_fta", ("sqrt(2) as root of x^2-2", \_ -> All.c_Re_observer (All.sqrt_two_fta All.Tt))),
  ("sqrt2", ("sqrt(2), second version", \_ -> All.sqrt_two_lcf All.Tt))]

usage :: () -> IO a
usage () = 
  do   
    putStr "usage: fta-test <test> <n>\n"
    putStr "where:\n"
    putStr " <n> is the rank of the approximation\n"
    putStr " <test> is one of the following tests:\n" 
    sequence_
     (map (\ (s1,(s2,_)) -> 
	   putStr ((replicate (12 - length s1) ' ')++s1++"\t "++s2))
      tests)
    System.exitFailure 

main = 
  do args <- System.getArgs 
     if length args /= 2 then usage () else return ()
     let 
      test = args!!0
      nb = (read (args!!1))::Integer
     case lookup test tests of 
      Nothing -> usage () 
      Just p -> 
        let 
         def = snd p
	 q = unsafeCoerce (All.r_observer (def ()) (i2n nb)) 
        in do
           putStr "the "
           putStr (show nb)
           putStr "-th approx of "
           putStr test
           putStr " is :\n"
           putStr (show (z2b (All.num q)))
           putStr " / "
           putStr (show (p2b (All.den q)))
           putStr "\n" 
