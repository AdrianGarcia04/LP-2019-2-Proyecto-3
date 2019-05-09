
module AlgoMM where

import Data.List
import Syntax

-- Dada una sustitución, elimina las que son de la forma x = x.
simpSus :: Subst -> Subst
simpSus sus = [(x, y) | (x, y) <- sus, V x /= y] -- Simplemente regresamos la
                                                 -- lista de sustituciones que
                                                 -- cumplan ser distintas

compSus :: Subst -> Subst -> Subst
compSus s1 s2 = zs ++ ws
    where zs = simpSus [(x, apsubT t s2) |  (x, t)  <- s1]
          ws = [(x, t) | (x, t) <- s2, not (elem x vs1)]
          vs1 = fst (unzip s1)

hazPares :: [a] -> [(a, a)]
hazPares l = case l of
    [] -> []
    x:y:xs -> (x, y):(hazPares (y:xs))
    x:xs -> []


unificaC_aux :: [(Term, Term)] -> Subst
unificaC_aux pares = case pares of
    [] -> []
    (t1, t2):lp -> case (t1, t2) of
        (F f lt1, F g lt2) -> if f == g && length lt1 == length lt2
                              then unificaC_aux((zip lt1 lt2) ++ lp) --DESC
                              else error "Imposible unificar" --DFALLA
        (V x , V y) -> if x == y
                       then unificaC_aux lp  --ELIM
                       else compSus d (unificaC_aux lps) -- SUST (Cuando t es variable)
          where d = [(x, V y)]
                lps = [(apsubT t1 d, apsubT t2 d) | (t1, t2) <- lp]
        (V x, F f lt) -> if elem x (varT (F f lt))
                         then error "Imposible unificar" --SFALLA
                         else compSus d (unificaC_aux lps) --(Cuando t es funcion)
          where d = [(x, F f lt)]
                lps = [(apsubT t1 d, apsubT t2 d) | (t1, t2) <- lp]
        (F f lt, V x) -> unificaC_aux ((t2, t1):lp) --SWAP

unificaConj :: [Term] -> Subst
unificaConj = unificaC_aux.hazPares

unifica :: Term -> Term -> Subst
unifica s t = unificaConj [s, t]


unificaLit :: Lit -> Lit -> Subst
unificaLit phi psi = case (phi, psi) of
    (TrueF, TrueF) -> []
    (FalseF, FalseF) -> []
    (Pr p lt1, Pr q lt2) -> if p == q && length lt1 == length lt2
                          then unificaC_aux (zip lt1 lt2)
                          else error "Imposible unificar"
    (Eq t1 s1, Eq t2 s2) -> unificaC_aux[(t1, t2),(s1, s2)]
    __ -> error "Imposible unificar"
