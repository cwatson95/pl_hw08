{-# LANGUAGE FlexibleInstances #-}

-- Implementation of the Syntax and Operational Semantics of the Pi Calculus

module Pi where

-- For documentation, see the following pages:
-- http://hackage.haskell.org/package/base-4.7.0.0/docs/Control-Concurrent.html
-- http://hackage.haskell.org/package/base-4.7.0.0/docs/Control-Concurrent-Chan.html

import Concurrent

import Control.Applicative
import Control.Monad
import Control.Monad.State

import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.List (concatMap)

-- Syntax of the Pi Calculus

type Name = String

instance Show (Chan Value) where
  show chan = "<channel>"

-- When reading through these data types, it is worth noting that *all* values
-- in this pi calculus are like locations in the STLC with references: they only
-- show up during evaluation, but *not* in programs a user might write.
--
-- In other words, the "abstract channel" object defined in your handout (as
-- "c" in the syntax) will actually be a Haskell channel (VChan below).  But
-- your translation will generate Pi terms, which only include expressions
-- (Exp), not values.

data Value
  = VChan (Chan Value)  -- channel value
  | VTup [Value]        -- tuple of values
  deriving Show

data Exp
  = EVar Name           -- variable expression
  | ETup [Exp]          -- tuple of expressions
  deriving Show

data Pattern
  = PVar Name           -- variable pattern
  | PTup [Pattern]      -- tuple pattern
  | Wild                -- wildcard pattern
  deriving Show

data Typ
  = TChan Typ           -- channel type
  | TTup [Typ]          -- tuple type
  deriving Eq

instance Show Typ where
  show (TChan t) = "Chan " ++ (show t)
  show (TTup []) = "()"
  show (TTup (h:ts)) = "(" ++ (show h) ++
    (concatMap (\x -> ", " ++ (show x)) ts) ++ ")"

instance Show (Env -> IO ()) where
  show f = "<function>"

data Pi
  = Nil
  | Pi :|: Pi
  | New Name Typ Pi
  | Out Name Exp
  | Inp Name Pattern Pi
  | RepInp Name Pattern Pi   -- repeated input
  | Embed (Env -> IO ()) Pi

instance Show Pi where
  show Nil = "0"
  show (p1 :|: p2) =
    "(" ++ (show p1) ++ ") | (" ++ (show p2) ++ ")"
  show (New x t p) =
    "new " ++ x ++ " : " ++ (show t) ++ ". " ++ (show p)
  show (Out x e) =
    "send " ++ x ++ "(" ++ (show e) ++ ")"
  show (Inp x pat p) =
    "rec " ++ x ++ "(" ++ (show pat) ++ "). " ++ (show p)
  show (RepInp x pat p) =
    "rec! " ++ x ++ "(" ++ (show pat) ++ "). " ++ (show p)
  show (Embed _ p) = "<function> " ++ (show p)

-- Useful Abbreviations

unitT :: Typ
unitT = TTup []

unitE :: Exp
unitE = ETup []

unitP :: Pattern
unitP = PTup []

printer :: String -> Pi
printer s = Embed (\_ -> putStr $ s ++ "\n") Nil

-- Static type checking

-- TASK!
-- Implement your pi calculus type checker here!


type Gamma = Map Name Typ

typeExp :: Gamma -> Exp -> Either String Typ
typeExp gamma (EVar name)
 | Map.member name gamma = Right $ gamma Map.! name
 | otherwise = Left $ "expression name untyped in contex" ++ show gamma 
typeExp gamma (ETup []) = Right $ TTup [] 
typeExp gamma (ETup es) = TTup <$> (sequence $ map (typeExp gamma) es)



typePat :: Gamma -> Pattern -> Typ -> Either String Gamma
typePat gamma (PVar name) typ = Right $ Map.insert name typ gamma
typePat gamma (PTup ps) (TTup ts) 
 | length ps == length ts = (foldl (\ gamma' (p,t) -> join $ (typePat <$> gamma' <*> (pure p) <*> (pure t))) (pure gamma) (zip ps ts))
 | otherwise = Left "ptup and ttup of unequal length"
typePat _ (PTup _) (TChan _) = Left "Attempting to match ptup to tchan"
typePat gamma Wild _ = Right gamma

--data Pi
--  = Nil
--  | Pi :|: Pi
--  | New Name Typ Pi
--  | Out Name Exp
--  | Inp Name Pattern Pi
--  | RepInp Name Pattern Pi   -- repeated input
--  | Embed (Env -> IO ()) Pi

checkPi :: Gamma -> Pi -> Either String ()
checkPi gamma Nil = Right ()
checkPi gamma (p1 :|: p2) = 
  let p1_check = checkPi gamma p1 
      p2_check = checkPi gamma p2
  in  (\ a b -> ()) <$> p1_check <*> p2_check
checkPi gamma (New name t p) = 
  let gamma' = Map.insert name t gamma -- ???
  in checkPi gamma' p
checkPi gamma (Out name e) 
  | Map.member name gamma = join $ check <$> (pure name_type) <*> e_type  
  | otherwise = Left $ name ++ " not found in context " ++ show gamma
  where name_type = gamma Map.! name
        e_type = typeExp gamma e
        check = (\ a b -> if a == b then Right () else Left $ outError name a e b gamma)
checkPi gamma (Inp name pat p) = 
  let typ = if Map.member name gamma 
            then Right $ gamma Map.! name
            else Left $ name ++ " not found in context " ++ show gamma
      gamma' = join $ typePat gamma pat <$> typ
  in  join $ checkPi <$> gamma' <*> (pure p)
checkPi gamma (RepInp name pat p) = checkPi gamma (Inp name pat p)
checkPi gamma (Embed _ p) = checkPi gamma p
 
--checkPi _ _ = Right ()
outError a a_t b b_t gamma = 
  "Types do not match \n" 
 ++ "Variable : " ++ show a ++ "\n"
 ++ "Variable type : " ++ show a_t ++ "\n"
 ++ "Expression : " ++ show b ++ "\n"
 ++ "Expression type : " ++ show b_t ++ "\n"
 ++ "Context : " ++ show gamma

check :: Pi -> Either String ()
check p = checkPi Map.empty p

-- Signals a dynamic error

type_error :: String -> a
type_error s = error $ "Run-time Type Error: " ++ s

-- Environments for interpreters

-- TASK!
-- Implement your interpreter here!



type Env = Map Name Value

-- evalPat env p v
-- match a value v against a pattern p and extend environment env
evalPat :: Env -> Pattern -> Value -> Env
evalPat env Wild _ = env
evalPat env (PVar name) val = Map.insert name val env
evalPat env (PTup pts) (VTup vls)
 | length pts == length vls = foldl (\ env' (pat',val') -> evalPat env' pat' val' ) env (zip pts vls) --length check????
 | otherwise = error $ "Pattern matching failed due to tuples of unequal length \n" 
                    ++ "Pattern : " ++ show (PTup pts) ++ "\n"
                    ++ "Value : " ++ show (VTup vls) ++ "\n"
evalPat env (PTup pts) (VChan v) = 
  error $ "Pattern matching failed \n"
       ++ "Pattern : " ++ show (PTup pts) ++ "\n"
       ++ "Value : " ++ show (VChan v)

-- evalExp env e
-- evaluates e to a value in environment env
evalExp :: Env -> Exp -> Value
evalExp env (EVar x) 
 | Map.member x env = env ! x
 | otherwise = error $ "Missing Variable:  " ++ x ++ "\n Curr Env:  " ++ show env
evalExp env (ETup es) = VTup (evalExps env es)
  where
    evalExps env [] = []
    evalExps env (e:es) = evalExp env e : evalExps env es

run :: Env -> Pi -> IO ()
run env Nil = do return ()
run env (p1 :|: p2) = parallel [(run env p1),(run env p2)]
run env (New name t p) =
  do c <- newChan 
     env' <- return $ Map.insert name ((VChan c)) env
     run env' p
run env (Out name exp) = do writeChan c val
   where (VChan c) = if Map.member name env then env Map.! name else error $ "Attempt to access chan that does not exist in env" 
         val = evalExp env exp 
run env (Inp name pat p) = 
  do val <- readChan c
     env' <- return $ evalPat env pat val
     run env' p
  where (VChan c) = if Map.member name env then env Map.! name else error $ "Attempt to access chan that does not exist in env" 
run env (RepInp name pat p) =
  do val <- readChan c
     env' <- return $ evalPat env pat val
     parallel [(run env' p),(run env (RepInp name pat p))]
  where (VChan c) = if Map.member name env then env Map.! name else error $ "Attempt to access chan that does not exist in env"
run env (Embed f p) = do f env
                         run env p

start :: Pi -> IO ()
start p = run Map.empty p



























