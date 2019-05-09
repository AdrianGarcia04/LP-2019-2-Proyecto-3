module Syntax where

import Data.List

-- Pueden definir cualquier otra funcion que consideren necesaria
-- o reutilizar cualquiera de las que definimos en proyectos anteriores.

type Ind = Int

type Nombre = String

type Subst = [(Ind, Term)]

data Term = V Ind | F Nombre [Term] deriving(Show,Eq)

-- Tipo de dato que representa literales
data Lit = TrueF
         | FalseF
         | Pr Nombre [Term]
         | Eq Term Term deriving (Show, Eq)

varT :: Term -> [Ind]
varT term = case term of
  V x -> [x]
  F _ l -> nub (concat [varT t | t <- l])

apsubT :: Term -> Subst -> Term
apsubT t sus = case t of
  V x -> case sus of
    [] -> V x
    (v, t2):xs -> if x == v
                  then t2
                  else apsubT (V x) xs
  F f lt -> F f [apsubT t sus | t <- lt]
