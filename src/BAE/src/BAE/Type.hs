{--
Practica 5
El lenguaje MiniC (MiniHS con efectos).
Módulo para definición y manejo de tipos.
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Type where

  import qualified Data.List as List

  -- | Se extiende la categoría de tipos.
  type Identifier = Int
  infix :->

  data Type = T Identifier
       | Integer | Boolean
       | Type :-> Type deriving (Show, Eq)

  type Substitution = [(Identifier, Type)]

  -- | Devuelve el conjunto de variables de tipo
  vars :: Type -> [Identifier]
  vars (T t) = [t]
  vars (t1 :-> t2) = List.union (vars t1) (vars t2)
  vars _ = []

  -- | Aplica la sustitución a un tipo dado
  subst :: Type -> Substitution -> Type
  subst e@(T t) s =
    case s of
      [] -> e
      ((x, t'): ss) ->
        if x == t then t' else subst e ss
  subst (t1 :-> t2) s = (subst t1 s) :-> (subst t2 s)
  subst t _ = t

  -- | Realiza la composición de dos sustituciones
  comp :: Substitution -> Substitution -> Substitution
  comp s1 s2 =
    List.union
    [(x, subst t s2) | (x, t) <- s1]
    [(x, t) | (x, t) <- s2, List.notElem x [y | (y, _) <- s1]]

  -- | Elimina sustituciones redundantes
  simpl:: Substitution -> Substitution
  simpl s = filter (\x -> not (redundant x)) s

  -- | Verifica si una tupla de una sustitución es reduntante. Auxiliar.
  redundant :: (Identifier, Type) -> Bool
  redundant (i, T t) = i == t
  redundant _ = False
