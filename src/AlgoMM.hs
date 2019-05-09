
module AlgoMM where

import Data.List
import Syntax

-- Dada una sustitución, elimina las que son de la forma x = x.
simpSus :: Subst -> Subst
simpSus sus = [(x, y) | (x, y) <- sus, V x /= y] -- Simplemente regresamos la
                                                 -- lista de sustituciones que
                                                 -- cumplan ser distintas

-- Dadas dos sustituciones, regresa su composición
compSus :: Subst -> Subst -> Subst
compSus s1 s2 = zs ++ ws                                    -- La composición es el
                                                            -- resultado de la concatenación
                                                            -- de las listas
    where zs = simpSus [(x, apsubT t s2) |  (x, t)  <- s1]  -- Pares de la aplicación
                                                            -- de la segunda sustitución
                                                            -- en los de la primera.
          ws = [(x, t) | (x, t) <- s2, not (elem x vs1)]    -- Pares de la segunda
                                                            -- sustitución donde
                                                            -- la variable a sustituir
                                                            -- no esté presente en las
                                                            -- las variables de la primera
          vs1 = fst (unzip s1)                              -- Obtenemos las variables
                                                            -- de la primer sustitución

-- Dada una lista, devuelve una lista de tuplas 2 a 2
hazPares :: [a] -> [(a, a)]
hazPares l = case l of
    [] -> []
    x:y:xs -> (x, y):(hazPares (y:xs))
    x:xs -> []

-- Dados un par de términos, devuelve la sustitución que los unifica
unificaC_aux :: [(Term, Term)] -> Subst
unificaC_aux pares = case pares of
    [] -> []
    (t1, t2):lp -> case (t1, t2) of
        (F f lt1, F g lt2) -> if f == g && length lt1 == length lt2    -- Si se trata
                                                                       -- de dos funciones iguales
                              then unificaC_aux((zip lt1 lt2) ++ lp)   -- Aplicamos la regla DESC
                              else error "Imposible unificar [DFALLA]" -- en otro caso, falla
        (V x , V y) -> if x == y                                       -- Si son dos variables iguales
                       then unificaC_aux lp                            -- aplicamos la regla de eliminación
                                                                       -- i.e. ignoramos y seguimos unificando
                       else compSus d (unificaC_aux lps)               -- en otro caso, aplicamos la regla SUST
                                                                       -- componiendo la sustitución obtenida 'd'
                                                                       -- y unificando el resto del nuevo conjunto
          where d = [(x, V y)]                                         -- La sustitución a componer
                lps = [(apsubT t1 d, apsubT t2 d) | (t1, t2) <- lp]    -- Obtenemos una nueva lista resultante
                                                                       -- de aplicar la sustitución 'd' al
                                                                       -- resto de los elementos.
        (V x, F f lt) -> if elem x (varT (F f lt))                     -- Si x está presente en
                                                                       -- las variables de la función
                         then error "Imposible unificar [SFalla]"      -- falla
                         else compSus d (unificaC_aux lps)             -- en otro caso, aplicamos la regla SUST
                                                                       -- componiendo la sustitución obtenida 'd'
                                                                       -- y unificando el resto del nuevo conjunto
          where d = [(x, F f lt)]                                      -- La sustitución a componer
                lps = [(apsubT t1 d, apsubT t2 d) | (t1, t2) <- lp]    -- Obtenemos una nueva lista resultante
                                                                       -- de aplicar la sustitución 'd' al
                                                                       -- resto de los elementos.
        (F f lt, V x) -> unificaC_aux ((t2, t1):lp)                    -- Si se trata de una función y una variable,
                                                                       -- las cambiamos de orden y seguimos unificando.

-- Dada una lista de términos, devuelve la sustitución que los unifica.
unificaConj :: [Term] -> Subst
unificaConj = unificaC_aux.hazPares

-- Dados dos términos, devuelve la sustitución que los unifica.
unifica :: Term -> Term -> Subst
unifica s t = unificaConj [s, t]

-- Dadas dos literales, devuelve la sustitución que las unifica.
unificaLit :: Lit -> Lit -> Subst
unificaLit phi psi = case (phi, psi) of
    (TrueF, TrueF) -> []
    (FalseF, FalseF) -> []
    (Pr p lt1, Pr q lt2) -> if p == q && length lt1 == length lt2      -- Si los predicados son iguales
                          then unificaC_aux (zip lt1 lt2)              -- buscamos la unificación de los
                                                                       -- elementos de cada predicado.
                          else error "Imposible unificar"              -- en otro caso, falla.
    (Eq t1 s1, Eq t2 s2) -> unificaC_aux[(t1, t2), (s1, s2)]           -- Si es una equivalencia,
                                                                       -- buscamos la unificación de
                                                                       -- los primeros elementos y los segundos.
    __ -> error "Imposible unificar"                                   -- en cualquier otro caso, falla.

unificaLit_aux :: [(Lit, Lit)] -> Subst
unificaLit_aux pares = case pares of
    [] -> []
    (l1, l2):lp -> case (l1, l2) of
        (TrueF, TrueF) -> unificaLit_aux lp                                                         -- Si son dos True, se ignoran y se continua
        (FalseF, FalseF) -> unificaLit_aux lp                                                       -- Análogo para False
        (TrueF, FalseF) -> error "Imposible unificar"                                               -- Si es un True y un False, es imposible unificar
        (FalseF, TrueF) -> error "Imposible unificar"                                               -- Análogo para False y True
        (Pr p lt1, Pr q lt2) -> if p /= q || length lt1 /= length lt2                               -- Si son dos predicados distintos
                                then error "Imposible unificar"                                     -- Falla
                                else compSus d (unificaLit_aux lps)                                 -- en otro caso, componemos la sustitución 'd'
                                                                                                    -- con la unificación del resto de literales,
                                                                                                    -- a las cuales se les aplica 'd'
                                where d = unificaC_aux (zip lt1 lt2)                                -- la sustitución 'd' a partir de la unificación
                                                                                                    -- de la lista de terminos de los predicados
                                      lps = [(apsubL lit1 d, apsubL lit2 d) | (lit1, lit2) <- lp]   -- La nueva lista de literales
                                                                                                    -- a las que se les aplica la sustitución 'd'
        (Eq l1 s1, Eq l2 s2) -> compSus d (unificaLit_aux lps)                                      -- Componemos la sustitución 'd'
                                                                                                    -- con la unificación del resto de literales,
                                                                                                    -- a las cuales se les aplica 'd'
                                where d = unificaC_aux[(l1, l2), (l1, s2)]                          -- la sustitución 'd' a partir de la unificación
                                                                                                    -- de los términos de las equivalencias
                                      lps = [(apsubL lit1 d, apsubL lit2 d) | (lit1, lit2) <- lp]   -- La nueva lista de literales
                                                                                                    -- a las que se les aplica la sustitución 'd'
        __ -> error "Imposible unificar"                                                            -- en cualquier otro caso, falla.

-- Dada una lista de literales, devuelve el unificador más general (umg)
mmE :: [Lit] -> Subst
mmE = unificaLit_aux.hazPares

-- Dada una lista de literales y una sustitución, devuelve la lista de literales
-- donde a cada literal se le ha aplicado la sustitución
sust_G :: [Lit] -> Subst -> [Lit]
sust_G l sus = case l of
    [] -> []
    x:xs -> nub ((apsubL x sus):(sust_G xs sus))

-- Dado una lista, devuelve su longitud
card :: [a] -> Int
card l = case l of
    [] -> 0
    x:xs -> 1 + (card xs)
