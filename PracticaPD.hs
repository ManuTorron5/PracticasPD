--PRÁCTICA LÓGICA PROPOSICIONAL
--PROGRAMACIÓN DECLARATIVA
--Manuel Sánchez Torrón

--DECLARACIÓN DE TIPOS
type Var = String --nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp deriving Read

--EJEMPLOS Y UTILIDADES

f1 = Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q")))) --tautologia
f2 = Y (V "p") (Si (No (V "q")) (No (V "p"))) -- satisf
f3 = Y (Y (V "p") (V "q")) (O (No (V "q")) (V "r")) --satisf
f4 = Y (V "p") (V "q")
f5 = No (O (No (V "p")) (No (V "q"))) -- f4 y f5 son equivalentes
taut = O (V "p") (No (V "p")) -- tautologia
cont = Y (V "p") (No (V "p")) --no satisf
l = ["p", "q", "r"]

--INSTANCIAS

instance Eq FProp where 
    (V v) == (V w) = v == w
    (No f) == (No g) = f == g
    (Y f g) == (Y p q) = (f == p) && (g == q) || (f == q) && (g == p)
    (O f g) == (O p q) = (f == p) && (g == q) || (f == q) && (g == p)
    (Si f g) == (Si p q) = (f == p) && (g == q)
    (Sii f g) == (Y p q) = (f == p) && (g == q) || (f == q) && (g == p)
    _ == _ = False

instance Ord FProp where
    f <= g = consecuencia g f -- f es menor que g si g es consecuencia de f

instance Show FProp where 
    show (V v) = v
    show (No f) = "~" ++ show f
    show (Y f g) = "(" ++ show f ++ " /\\ " ++ show g ++ ")"
    show (O f g) = "(" ++ show f ++ " \\/ " ++ show g ++ ")"
    show (Si f g) = "(" ++ show f ++ " -> " ++ show g ++ ")"
    show (Sii f g) = "(" ++ show f ++ " <-> " ++ show g ++ ")"

--FUNCIONES

--vars devuelve la lista de variables de una fórmula
vars :: FProp -> [Var]
vars f = varsAux f []

varsAux :: FProp -> [Var] -> [Var]
varsAux (V v) list = 
    if (elem v list) then list 
    else v:list
varsAux (No f) list = varsAux f list
varsAux (Y f g) list = let list1 = (varsAux f list) in (varsAux g list1)
varsAux (O f g) list = let list1 = (varsAux f list) in (varsAux g list1)
varsAux (Si f g) list = let list1 = (varsAux f list) in (varsAux g list1)
varsAux (Sii f g) list = let list1 = (varsAux f list) in (varsAux g list1)

--varsAux utiliza list como una lista en la que se acumulan las variables.
--Para las constructoras Y, O, Si y Sii, primero se genera la lista list1 con las variables de la primera frase
--y con ella como parámetro de entrada se generan las variables de la 2a frase

--evaluar f list devuelve la evaluacion de f siendo list del tipo [(Var, Bool)], que indica el valor que 
--se le asigna a cada variable
evaluar :: FProp -> [(Var, Bool)] -> Bool
evaluar (V v) (x:xs) = 
    if (v == (fst x)) then (snd x) 
    else (evaluar (V v) xs)
evaluar (No f) l = not (evaluar f l)
evaluar (Y f g) l = (evaluar f l) && (evaluar g l)
evaluar (O f g) l = (evaluar f l) || (evaluar g l)
evaluar (Si f g) l = not ((evaluar f l) && not (evaluar g l)) -- (f -> g) es falso cuando f T y g F
evaluar (Sii f g) l = (evaluar f l) == (evaluar g l) 

--lista con todas las asignaciones posibles de una lista de variables
-- ejemplo: asignaciones ["p", "q"] = [[("p", False), ("q", False)],[("p", False), ("q", True)], [("p", True), ("q", False)], [("p", True), ("q", True)]]
asignaciones :: [Var] -> [[(Var, Bool)]]
asignaciones [] = [[]]
asignaciones (v:vs) = let xs = asignaciones vs in [(v,False):ys| ys<-xs] ++ [(v,True):ys| ys <- xs]

-- tautologia f devuelve True si f es una tautologia
tautologia :: FProp -> Bool 
tautologia f = tautologiaAux f (asignaciones (vars f))

tautologiaAux :: FProp -> [[(Var, Bool)]] -> Bool
tautologiaAux f [] = True
tautologiaAux f (xs:xss) = (evaluar f xs) && (tautologiaAux f xss)

--satisfactible f devuelve True si f es satisfactible
satisfactible :: FProp -> Bool 
satisfactible f = satisfactibleAux f (asignaciones (vars f))

satisfactibleAux :: FProp -> [[(Var,Bool)]] -> Bool
satisfactibleAux f [] = False
satisfactibleAux f (xs:xss) = (evaluar f xs) || (satisfactibleAux f xss) 

--consecuencia f g devuelve True si f es consecuencia logica de g
consecuencia :: FProp -> FProp -> Bool
consecuencia f g = tautologia (Si g f)

--equivalentes f g devuelve True si f y g son logicamente equivalentes
equivalentes :: FProp -> FProp -> Bool
equivalentes f g = tautologia (Sii f g)

--consecuencias l devuelve una lista de pares cuyo primer elemento f es cada formula de l
--y cuyo segundo elemento es una lista con todas las consecuencias de f que están en l
--Nota : como f->f, en cada lista de consecuencias está la propia fórmula
consecuencias :: [FProp] -> [(FProp, [FProp])]
consecuencias fs = consecuenciasAux fs (length fs)

consecuenciasAux :: [FProp] -> Int -> [(FProp, [FProp])]
consecuenciasAux fs 0 = []
consecuenciasAux fs n = let x = fs !! (length fs - n) in  [(x,[f| f <- fs , consecuencia f x])] ++ consecuenciasAux fs (n-1) 

-- Idea: como necesitamos la lista completa siempre utilizamos (n-length fs) como indicador de
-- posición. Recorremos la lista fs y guardamos en x la frase de fs en la posición (length fs - n). 
-- Luego, hacemos una lista en la que los elementos serán pares, en los cuales el primer elemento
--es x y el segundo la lista de frases de fs que son consecuencia de x. Luego llamamos a consecuenciasAux
-- con la siguiente posición de fs



--equivalencias l devuelve una lista de listas que representa el conjunto cociente de la lista l
-- con la relación de ser equivalentes. Es decir cada elemento de la lista resultante es el conjunto 
-- de formulas equivalentes entre sí de la lista original
equivalencias :: [FProp] -> [[FProp]]
equivalencias fs = equivalenciasAux fs

equivalenciasAux :: [FProp] -> [[FProp]]
equivalenciasAux [] = []
equivalenciasAux (f:fs) = [g | g <- (f:fs) , equivalentes f g] : equivalenciasAux (quitaEquivalentes f fs)

--Idea: Cogemos la clase de equivalencia del primer elemento de la lista, y llamamos de nuevo a la funcion
-- con lo que queda de eliminar de la lista original la clase de equivalencia que acabamos de sacar

--quitaEquivalentes f l elimina de l las formulas equivalentes a f
quitaEquivalentes :: FProp -> [FProp] -> [FProp]
quitaEquivalentes f [] = []
quitaEquivalentes f (g:gs) = if (equivalentes f g) then quitaEquivalentes f gs
                             else g:(quitaEquivalentes f gs)



--INTERACCIÓN CON EL USUARIO
--Llamar a main para iniciar

--leer un entero
getInt:: IO Int
getInt = do line <- getLine
            return (read line::Int)

--leer una lista de formulas
getFormulas :: Int -> IO [FProp]
getFormulas 0 = return []
getFormulas n = do line <- getLine
                   frases <- getFormulas (n-1)
                   return ((read line::FProp):frases)

-- escribe la lista de fórmulas con los correspondientes índices
-- el primer parámetro es la lista inalterada para llamar de nuevo a getOpcion al acabar
putFormulas:: [FProp] -> Int -> IO ()
putFormulas [] n = do putStr ""
putFormulas (f:fs) n = do putStrLn ((show n) ++ ": " ++ show f)
                          putFormulas fs (n+1)



-- getOpcion pide una de las posibles acciones sobre formulas de la lista introducida y 
-- llama a la funcion io correspondiente
getOpcion :: [FProp] -> IO ()
getOpcion fs = do putStrLn "¿Qué desea hacer? (Introduzca el número correspondiente)"
                  putStrLn "1. Variables"
                  putStrLn "2. Tautología"
                  putStrLn "3. Satisfactible"
                  putStrLn "4. Consecuencia"
                  putStrLn "5. Equivalente"
                  putStrLn "6. Lista de consecuencias"
                  putStrLn "7. Lista de equivalencias"
                  putStrLn "8. Mostrar la lista de fórmulas"
                  putStrLn "9. Resetear"
                  putStrLn "10. Salir"
                  n <- getInt
                  if (n <= 0 || n > 10) then getOpcion fs
                  else if (n == 1) then  io_vars fs 
                  else if (n == 2) then io_tautologia fs
                  else if (n == 3) then io_satisfactible fs
                  else if (n == 4) then io_consecuencia fs 
                  else if (n == 5) then io_equivalentes fs
                  else if (n == 6) then do print $ consecuencias fs
                                           getOpcion fs
                  else if (n == 7) then do print $ equivalencias fs
                                           getOpcion fs
                  else if (n == 8) then do putStrLn "Lista de fórmulas:"
                                           putFormulas fs 0
                                           getOpcion fs
                  else if (n == 9) then main
                  else return ()



-- Las funciones io piden uno o dos índices según corresponda y ejecuta la accion 
-- con las formulas correspondientes a los índices
io_vars :: [FProp] -> IO ()
io_vars fs = do putStrLn "¿Con qué fórmula? (Introduzca el número correspondiente)"
                n <- getInt
                print $ vars (fs !! n)
                getOpcion fs
                return () 


io_tautologia :: [FProp] -> IO ()
io_tautologia fs = do putStrLn "¿Con qué fórmula? (Introduzca el número correspondiente)"
                      n <- getInt
                      print $ tautologia (fs !! n)
                      getOpcion fs
                      return () 


io_satisfactible :: [FProp] -> IO ()              
io_satisfactible fs = do putStrLn "¿Con qué fórmula? (Introduzca el número correspondiente)"
                         n <- getInt
                         print $ satisfactible (fs !! n)
                         getOpcion fs
                         return () 


io_consecuencia :: [FProp] -> IO ()
io_consecuencia fs = do putStrLn "¿Con qué fórmulas? (Introduzca el número correspondiente)"
                        n <- getInt
                        m <- getInt
                        print $ consecuencia (fs !! n) (fs !! m)
                        getOpcion fs
                        return () 


io_equivalentes :: [FProp] -> IO ()
io_equivalentes fs = do putStrLn "¿Con qué fórmulas? (Introduzca el número correspondiente)"
                        n <- getInt
                        m <- getInt
                        print $ equivalentes (fs !! n) (fs !! m)
                        getOpcion fs
                        return () 
                                  

main :: IO ()
main = do putStrLn "¿Cuantas fórmulas desea introducir?"
          n <- getInt
          putStrLn "Introduzca las fórmulas:"
          lista <- (getFormulas n)
          getOpcion lista
          return ()