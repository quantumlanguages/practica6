{--
Practica 5
El lenguaje MiniC (MiniHS con efectos). Memoria
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Memory where

    import BAE.Sintax

    -- | Definiendo tipos y alias para trabajar con memoria
    type Address = Int
    type Value = Expr
    type Cell = (Address, Value)
    type Memory = [Cell]

    -- | Genera una uneva dirección de memoria que no esté en la lista
    newAddress :: Memory -> Expr
    newAddress m =
        if checkMemory m
            then newAddressAux m 0
            else error "Corrupted memory"

    -- | Revisa si una dirección de memoria está en una lista. Si es el caso,
    -- incrementa la dirección y sigue buscando
    newAddressAux :: Memory -> Address -> Expr
    newAddressAux [] i = L i
    newAddressAux m@((l, v):ms) i =
        if i == l
            then newAddressAux m (i+1)
            else newAddressAux ms i

    -- | Devuelve el valor guardado en memoria
    access :: Address -> Memory -> Maybe Value
    access i m =
        if checkMemory m
            then accessUnsafe i m
            else error "Corrupted memory"

    -- | Devuelve el valor guardado sin revisar la integridad de la memoria
    accessUnsafe :: Address -> Memory -> Maybe Value
    accessUnsafe _ [] = Nothing
    accessUnsafe i ((l, v):ms) =
        if i == l
            then Just v
            else accessUnsafe i ms

    -- | Revisa si la memoria es válida
    checkMemory :: Memory -> Bool
    checkMemory [] = True
    checkMemory ((l, v):ms) =
        case (filter (\(m, u) -> m == l) ms) of
            [] -> checkMemory ms
            _ -> False

    -- | Actualiza el valor de una celda
    update :: Cell -> Memory -> Maybe Memory
    update (i, k) m =
     if checkMemory m
                then
                  case k of
                    I n -> updateUnsafe (i, k) [] m
                    B p -> updateUnsafe (i, k) [] m
                    Fn x e -> updateUnsafe (i, k) [] m
                    L i -> updateUnsafe (i, k) [] m
                    _ -> error "Memory can only store values"
                else error "Corrupted memory"


    -- | Actualiza el valor de una celda sin revisar la integridad de la memoria
    -- no de los valores a guardar
    updateUnsafe :: Cell -> Memory -> Memory -> Maybe Memory
    updateUnsafe _ _ [] = Nothing
    updateUnsafe n@(i, k) acc (h@(l, v):ms) =
        if i == l
            then Just (acc ++ (n:ms))
            else updateUnsafe n (acc ++ [h]) ms
