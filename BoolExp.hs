{-
Syntax and Implementation of Boolean Expressions
================================================
-}

module BoolExp where

import Pi
import qualified Data.Map.Strict as M

data BoolExp
  = BVar Name
  | BVal Bool
  | BoolExp :&&: BoolExp
  | BoolExp :||: BoolExp
  | Not BoolExp
  deriving Show

-- Environments for interpreting boolean expressions
type BEnv = M.Map Name Bool

-- TASK!!!
-- compileBExp tchan fchan b
-- returns a process p that when juxtaposed with a compatible environment
-- sends a message on tchan if the boolean expression evaluates to true
-- sends a message on fchan if the boolean expression evaluates to false

compileBExp :: Name -> Name -> BoolExp -> Pi
compileBExp tchan fchan (BVar name)  = name_t :|: name_f 
  where name_t = Inp (name ++ "_t") unitP $ Out tchan unitE
        name_f = Inp (name ++ "_f") unitP $ Out fchan unitE
compileBExp tchan fchan (BVal bool)  = if bool then Out tchan unitE else Out fchan unitE
compileBExp tchan fchan (b1 :&&: b2) = compileBExp tchan fchan $ Not $ Not b1 :||: Not b2 
compileBExp tchan fchan (b1 :||: b2) = New tchan' unitT $ New fchan' unitT $ or_p
  where tchan' = tchan ++ "t"
        fchan' = fchan ++ "f"
        b1_p = (compileBExp tchan' fchan' b1)
        b2_p = (compileBExp tchan' fchan' b2)
        true = Inp tchan' unitP $ Out tchan unitE
        false = Inp fchan' unitP $ Inp fchan' unitP $ Out fchan unitE 
        or_p = (b1_p :|: b2_p) :|: (true :|: false)  
compileBExp tchan fchan (Not b)      = compileBExp fchan tchan b 



-- TASK!!!!
-- compile a boolean variable environment into a process that
-- communicates with a compiled Boolean expression containing free
-- variables from the environment

compileBExpEnv :: BEnv -> Pi -> Pi
compileBExpEnv benv p = foldr (\ (name,bool) xs -> New (name ++ "_t") unitT $ New (name ++ "_f") unitT xs) b_p x  
  where x = (M.toList benv) 
        out = combineProcesses $ map toSignal x 
        b_p = (out :|: p)


-- NOTE!!!!
-- This implementation works for all names except for the two reserverd names
-- "t" and "f"
toSignal :: (Name,Bool) -> Pi
toSignal (name,True) = Out (name ++ "_t") unitE
toSignal (name,False) = Out (name ++ "_f") unitE 

combineProcesses :: [Pi] -> Pi
combineProcesses [] = Nil
combineProcesses (x:xs) = x :|: (combineProcesses xs)

startBool :: BEnv -> BoolExp -> IO ()
startBool benv bexp =
  start pi
    where
      tchan = "t"
      fchan = "f"
      pi = New tchan unitT $
           New fchan unitT $
           compileBExpEnv benv (compileBExp tchan fchan bexp) :|:
           Inp tchan unitP (printer "true") :|:
           Inp fchan unitP (printer "false")
