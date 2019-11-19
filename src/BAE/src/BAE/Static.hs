{--
Practica 5
El lenguaje MiniC (MiniHS con efectos).
Módulo para el análisis estáticos de expresiones. (i.e. Revisión de tipos)
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Static where

  import qualified Data.List as List
  import qualified BAE.Type as Type
  import qualified BAE.Unifier as Unifier
  import  qualified BAE.Sintax as Sintax

  -- | Definiendo el contexto para tipos de variables
  type Ctxt = [(Sintax.Identifier, Type.Type)]

  -- | Definiendo las restricciones para inferir los tipos
  type Constraint = [(Type.Type, Type.Type)]

  -- | Realiza sustituciones de variables de tipo
  subst :: Ctxt -> Type.Substitution -> Ctxt
  subst [] _ = []
  subst ((x, t): cs) s = (x, Type.subst t s) : subst cs s

  -- | Busca el tipo de una variable en un contexto
  find :: Sintax.Identifier -> Ctxt -> Maybe Type.Type
  find _ [] = Nothing
  find x ((y, t) : cs) =
    if x == y
      then Just t
      else find x cs

  -- | Obtiene una variable que no figure en la lista
  fresh :: [Type.Type] -> Type.Type
  fresh s =
    Type.T ((foldl max 0 (foldr (\ x y -> List.union (Type.vars x) y) [] s)) + 1)


  -- | Dada una expresión (con un acumulador de variables de tipo), devuelve el
  -- el tipo más general sin restricciones, las restricciones que faltan y el
  -- contexto donde el tipo es válido
  infer' :: ([Type.Type], Sintax.Expr) -> ([Type.Type], Ctxt, Type.Type, Constraint)
  -- variables
  infer' (nv, (Sintax.V x)) =
    let t = fresh nv; nv' = nv `List.union` [t]
      in (nv' ,[(x, t)] ,t , [])

  -- integer
  infer' (nv, (Sintax.I n)) = (nv, [], Type.Integer, [])

  -- bool
  infer' (nv, (Sintax.B p)) = (nv, [], Type.Boolean, [])

  --functions
  infer' (nv, (Sintax.Fn x e)) =
    let (nv', g, t, r) = infer' (nv, e)
      in case find x g of
        Just t' -> (nv', filter (\(i, t) -> i /= x) g, t' Type.:-> t, r)
        Nothing ->
          let t' = fresh nv'; nv'' = nv' `List.union` [t']
            in (nv'', g, t' Type.:-> t, r)

  -- succ
  infer' (nv, (Sintax.Succ n)) =
    let (nv', g, t, r) = infer' (nv, n)
      in (nv', g, Type.Integer, (t, Type.Integer):r)

  -- pred
  infer' (nv, (Sintax.Pred n)) =
    let (nv', g, t, r) = infer' (nv, n)
      in (nv', g, Type.Integer, (t, Type.Integer):r)

  -- not
  infer' (nv, (Sintax.Not p)) =
    let (nv', g, t, r) = infer' (nv, p)
      in (nv', g, Type.Boolean, (t, Type.Boolean):r)

  -- add
  infer' (nv, (Sintax.Add e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Integer,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Integer), (t2, Type.Integer)]

            ) --items

  -- mul
  infer' (nv, (Sintax.Mul e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Integer,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Integer), (t2, Type.Integer)]

            ) --items

  -- and
  infer' (nv, (Sintax.And e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Boolean,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Boolean), (t2, Type.Boolean)]

            ) --items

  -- or
  infer' (nv, (Sintax.Or e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Boolean,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Boolean), (t2, Type.Boolean)]

            ) --items

  -- lt
  infer' (nv, (Sintax.Lt e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Boolean,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Integer), (t2, Type.Integer)]

            ) --items

  -- gt
  infer' (nv, (Sintax.Gt e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Boolean,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Integer), (t2, Type.Integer)]

            ) --items

  -- eq
  infer' (nv, (Sintax.Eq e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
          in (
              nv2,
              g1 `List.union` g2,
              Type.Boolean,
              r1 `List.union` r2 `List.union` s
              `List.union` [(t1, Type.Integer), (t2, Type.Integer)]

            ) --items

  -- if
  infer' (nv, (Sintax.If e1 e2 e3)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        (nv3, g3, t3, r3) = infer' (nv2, e3);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
          `List.union`
            [(s1, s2) | (x, s1) <- g1, (y, s2) <- g3, x == y]
          `List.union`
            [(s1, s2) | (x, s1) <- g2, (y, s2) <- g3, x == y];
        z = fresh nv3; --item para operadores
        nv' = nv3 `List.union` [z]
          in (
              nv',
              g1 `List.union` g2 `List.union` g3,
              z,
              r1 `List.union` r2 `List.union` r3 `List.union` s
              `List.union` [(t1, Type.Boolean), (t2, z), (t3, z)]
            ) --items

  -- app
  infer' (nv, (Sintax.App e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y];
        z = fresh nv2; --item para operadores
        nv' = nv2 `List.union` [z]
          in (
              nv',
              g1 `List.union` g2,
              z,
              r1 `List.union` r2 `List.union` s `List.union` [(t1, t2 Type.:-> z)]

            ) --items
  --let
  infer' (nv, (Sintax.Let x e1 e2)) =
    let (nv1, g1, t1, r1) = infer' (nv, e1);
        (nv2, g2, t2, r2) = infer' (nv1, e2);
        (nv3, g3, t3) =
          case find x g2 of
            Just t' -> (nv2, filter (\(i, t) -> i /= x) g2, t')
            Nothing -> (nv2 `List.union` [t'], g2, t') where t' = fresh nv2;
        s = [(s1, s3) | (x, s1) <- g1, (y, s3) <- g3, x == y];
        in (
          nv3,
          g1 `List.union` g3,
          t2,
          r1 `List.union` r2 `List.union` s `List.union` [(t1, t3)]
        )

  -- | Dada una expresión, infiere su tipo devolviendo el contexto donde es valido.
  infer :: (Sintax.Expr) -> (Ctxt, Type.Type)
  infer e =
    let (_, g, t, r) = infer' ([], e); umg = Unifier.µ r
      in (subst g (head umg), Type.subst t (head umg))
