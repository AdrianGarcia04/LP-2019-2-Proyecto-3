module Syntax where

import Data.List

-- Definimos los indices como sinónimos de enteros, para usarlos como variables.
type Ind = Int

-- Definimos los nombres de funciones y predicados como cadenas.
type Nombre = String

-- Definimos las sustituciones como una lista de tuplas, con una variable como
-- primer miembro, y un término como segundo miembro.
type Subst = [(Ind, Term)]

-- Definimos lo términos como variables o funciones con una lista de términos
data Term = V Ind | F Nombre [Term] deriving(Show,Eq)

-- Tipo de dato que representa literales
data Lit = TrueF
         | FalseF
         | Pr Nombre [Term]
         | Eq Term Term deriving (Show, Eq)

-- Dado un término, devuelve su lista de variables
varT :: Term -> [Ind]
varT term = case term of
  V x -> [x]
  F _ l -> nub (concat [varT t | t <- l])

-- Dado un término y una sustitución, devuelve un nuevo término con la
-- sustitución aplicada.
apsubT :: Term -> Subst -> Term
apsubT t sus = case t of
  V x -> case sus of
    [] -> V x
    (v, t2):xs -> if x == v                 -- Si la sustitución aplica
                  then t2                   -- regresamos solo el segundo miembro
                  else apsubT (V x) xs      -- en otro caso, continuamos
  F f lt -> F f [apsubT t sus | t <- lt]    -- Si es una función, aplicamos la
                                            -- sustitución a cada elemento
