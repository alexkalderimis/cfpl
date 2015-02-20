-- Code from chapter 9 - A Type Checker

-- The main thing is working through the code to make it more comprehensible my using
-- modern things like maps, monads, type-aliases and sensible var names (gamma?, pls).

-- The amazing thing about this is that it works. I wrote it, made it compile,
-- but I still don't entirely understand it.

import qualified Data.Map as Map

get = (Map.!) -- rename symbol

type VarName = String

data Exp = Var VarName
            | Lambda VarName Exp
            | Apply Exp Exp
            | Let [VarName] [Exp] Exp
            | LetRec [VarName] [Exp] Exp
            deriving (Show, Eq)

type TypeName = [Int]

data TypeExp = TypeVar TypeName
            | TypeCons String [TypeExp]
            deriving (Show, Eq)

-- Built in types.

arrow t1 t2 = TypeCons "arrow" [t1, t2]
int = TypeCons "int" []
cross t1 t2 = TypeCons "cross" [t1, t2]
list t = TypeCons "list" [t]

varsIn :: TypeExp -> [TypeName]
varsIn t = varsIn' t []
            where varsIn' (TypeVar x)     vars = x:vars
                  varsIn' (TypeCons _ ts) vars = foldr varsIn' vars ts

type Substitution = TypeName -> TypeExp

subType :: Substitution -> TypeExp -> TypeExp
subType phi (TypeVar name) = phi name
subType phi (TypeCons con ts) = TypeCons con (map (subType phi) ts)

-- Using maybes - no error messages for you!
type Unification = Maybe Substitution

scomp :: Substitution -> Substitution -> Substitution
scomp phi psi name = subType phi (psi name)

idSubst :: Substitution
idSubst name = TypeVar name

deltaSubst :: TypeName -> TypeExp -> Substitution
deltaSubst name t asName
    | name == asName = t
    | otherwise      = TypeVar asName

extend :: Substitution -> TypeName -> TypeExp -> Unification
extend phi name t
    | t == TypeVar name    = Just phi
    | elem name (varsIn t) = Nothing
    | otherwise            = Just $ (deltaSubst name t) `scomp` phi

type Equation = (TypeExp, TypeExp)

unify :: Substitution -> Equation -> Unification
unify phi ((TypeVar name), t2)
    | phiret == TypeVar name = extend phi name subt
    | otherwise              = unify phi (phiret, subt)
    where phiret = phi name
          subt   = subType phi t2

unify phi ((TypeCons conname ts), (TypeVar varname)) = unify phi ((TypeVar varname), (TypeCons conname ts))

unify phi ((TypeCons conA tsA), (TypeCons conB tsB))
    | conA == conB = unifyl phi (tsA `zip` tsB)
    | otherwise    = Nothing

unifyl :: Substitution -> [Equation] -> Unification
unifyl phi eqns = foldr unify' (Just phi) eqns
    where unify' eqn (Just p) = unify p eqn
          unify' eqn Nothing  = Nothing

-- A type scheme lists the schematic (generic) type variable names associated with a type
data Scheme = Scheme [TypeName] TypeExp
                deriving (Show, Eq)

unknowns :: Scheme -> [TypeName]
unknowns (Scheme schematics t) = nonSchematic $ varsIn t
    where nonSchematic = filter (`notElem` schematics)

subScheme :: Substitution -> Scheme -> Scheme
subScheme phi (Scheme schematics t) = Scheme schematics (subType exclude t)
    where exclude name = if name `elem` schematics then (TypeVar name) else (phi name)

-- Type environments (where we look up the type schemes)

type Env = Map.Map VarName Scheme

unknownsInEnv :: Env -> [TypeName]
unknownsInEnv env = concatMap unknowns (Map.elems env)

subEnv :: Substitution -> Env -> Env
subEnv phi = Map.map (subScheme phi)

-- Name supplies - lazy sequences of unique identifiers

nextName :: NameSupply -> TypeName
deplete :: NameSupply -> NameSupply
split :: NameSupply -> (NameSupply, NameSupply)

type NameSupply = TypeName
nextName = id
deplete (n:ns) = (n+2:ns)
split ns = (0:ns,1:ns)

-- Infinite list of ids
nameSequence :: NameSupply -> [TypeName]
nameSequence ns = nextName ns : nameSequence (deplete ns)

-- The type checker

type TypeCheckResult = Maybe (Substitution, TypeExp)

typeCheck :: Env -> NameSupply -> Exp -> TypeCheckResult

typeCheck env ns (Var x) = tcVar env ns x
typeCheck env ns (Apply e1 e2) = tcApp env ns e1 e2
typeCheck env ns (Lambda vs e) = tcLamda env ns vs e
typeCheck env ns (Let xs es e) = tcLet env ns xs es e
typeCheck env ns (LetRec xs es e) = tcLetRec env ns xs es e

-- Helper to check all types in a list.
checkAll :: Env -> NameSupply -> [Exp] -> Maybe (Substitution, [TypeExp])
checkAll env ns [] = Just (idSubst, [])
checkAll env ns (e:es) = do
    let (ns0, ns1) = split ns
    (phi, t) <- typeCheck env ns0 e -- Check the first expression
    (psi, ts) <- checkAll (subEnv phi env) ns1 es -- Check the rest of the types
    return (combineTypeCheckResults phi t psi ts) -- Combine with all the rest

-- Combine a single type check result with a list of type check results.
-- The involves combining the substitutions and joining the lists (subtyped)
combineTypeCheckResults :: Substitution -> TypeExp -> Substitution -> [TypeExp] -> (Substitution, [TypeExp])
combineTypeCheckResults phi t psi ts = ((psi `scomp` phi), (subType psi t) : ts)

-- Check variables
tcVar :: Env -> NameSupply -> VarName -> TypeCheckResult
tcVar env ns x = do
    scheme <- Map.lookup x env
    return (idSubst, newInstance ns scheme)

newInstance :: NameSupply -> Scheme -> TypeExp
newInstance ns (Scheme vars t) = subType phi t
    where m = Map.fromList $ vars `zip` (nameSequence ns)
          phi = mappingSubst m

-- Substitution that retrieves var from map if present.
mappingSubst :: Map.Map TypeName TypeName -> Substitution
mappingSubst al tvn
    | Map.member tvn al = TypeVar (al `get` tvn) -- One of the schematic vars, get new var
    | otherwise         = TypeVar tvn            -- free var, leave unchanged

newScheme :: TypeName -> Scheme
newScheme tn = Scheme [] (TypeVar tn)

-- Check applications
tcApp :: Env -> NameSupply -> Exp -> Exp -> TypeCheckResult
tcApp env ns e1 e2 = do
    let tvn = nextName ns
    let ns' = deplete ns
    (phi, [t1, t2]) <- checkAll env ns' [e1, e2] -- Check types of expressions
    psi <- unify phi (t1, t2 `arrow` (TypeVar tvn)) -- Solve with new constraint
    return (psi, psi tvn)

-- check lambda abstractions

tcLamda :: Env -> NameSupply -> VarName -> Exp -> TypeCheckResult
tcLamda env ns x e = do
    let tvn = nextName ns
    let ns' = deplete ns
    let env' = Map.insert x (newScheme tvn) env
    (phi, t) <- typeCheck env' ns' e -- Check the expression
    return (phi, arrow (phi tvn) t)

-- Check let expressions

-- type check the defs, update the env to include these bindings, check
-- the rhs, and then combine the results.
tcLet :: Env -> NameSupply -> [VarName] -> [Exp] -> Exp -> TypeCheckResult
tcLet env ns vars vals e = do
    let (ns0, ns1) = split ns
    let (ns2, ns3) = split ns1
    (phi, ts) <- checkAll env ns0  vals
    let env' = withBindings (subEnv phi env) ns2 vars ts
    (psi, t) <- typeCheck env' ns3 e
    return (psi `scomp` phi, t)

withBindings :: Env -> NameSupply -> [VarName] -> [TypeExp] -> Env
withBindings env ns names types =
    Map.union newTypes env
    where newTypes = Map.fromList (names `zip` schemes)
          schemes = map (createScheme varFilter ns) types
          varFilter = filter $ not . (`elem` unknowns)
          unknowns = unknownsInEnv env

createScheme :: ([TypeName] -> [TypeName]) -> NameSupply -> TypeExp -> Scheme
createScheme filt ns t = Scheme (map snd bindings) t'
    where bindings = zip schematics (nameSequence ns)
          schematics = filt $ uniq (varsIn t)
          t' = subType (mappingSubst (Map.fromList bindings)) t

uniq :: Eq a => [a] -> [a]
uniq xs = f [] xs
    where f acc [] = acc
          f acc (x:xs)
            | x `elem` acc = f acc xs
            | otherwise    = f (x:acc) xs

tcLetRec :: Env -> NameSupply -> [VarName] -> [Exp] -> Exp -> TypeCheckResult
tcLetRec env ns names vals e = do
    let (ns', ns1) = split ns
    let (ns2, ns3) = split ns'
    let (ns4, ns5) = split ns3
    let boundSchemes = bindNames names ns1
    (phi, ts) <- checkAll (Map.union boundSchemes env) ns2 vals
    let boundSchemes' = subEnv phi boundSchemes
    let env' = subEnv phi env
    let ts' = map getSchemeType $ Map.elems boundSchemes'
    unifier <- unifyl phi (ts `zip` ts')
    let unifiedBindings = (subEnv unifier boundSchemes')
    let unifiedTypes = map getSchemeType (Map.elems unifiedBindings)
    let fullEnv = withBindings (subEnv unifier env') ns4 (Map.keys unifiedBindings) unifiedTypes
    (psi, t) <- typeCheck fullEnv ns5 e
    return (psi `scomp` unifier, t)

getSchemeType (Scheme [] t) = t

bindNames names ns = Map.map newScheme namesToTypeNames
    where namesToTypeNames = Map.fromList $ names `zip` (nameSequence ns)

-- skk should be the same as id

fn vars e = foldr Lambda e vars

skk :: Exp
skk = Let ["s", "k"] [s_def, k_def] body
    where var_s = Var "s"
          var_k = Var "k"
          var_x = Var "x"
          var_y = Var "y"
          var_z = Var "z"
          body = Apply (Apply var_s var_k) var_k
          s_def = fn ["x", "y", "z"] body_s
          k_def = fn ["x", "y"] body_k
          body_s = Apply (Apply var_x var_z) (Apply var_y var_z)
          body_k = var_x

sndExp :: Exp
sndExp = fn ["x", "y"] (Var "y")

idExp :: Exp
idExp = fn ["x"] (Var "x")

badFn :: Exp
badFn = fn ["a"] (Var "b")

onePlusOne = Apply double one
    where double = fn ["x"] (Apply (Apply (Var "add") (Var "x")) (Var "x"))
          one = Var "1"

builtIns :: (NameSupply, Env)
builtIns = (ns', Map.fromList [("1", intScheme), ("add", addScheme)])
    where ns = [0]
          ns' = deplete ns
          intType = TypeVar (nextName ns)
          intScheme = Scheme [] intType
          addScheme = Scheme [] (arrow intType (arrow intType intType))

getType = getTypeInEnv ([0], Map.empty)
getTypeInEnv (ns, env) e = fmap snd (typeCheck env ns e)

-- id should have the same signature as skk, even though skk is *much* more complex.
main = do
    -- Should be (arrow x (arrow y) y)
    print sndExp
    print $ getType sndExp
    -- Should be nothing
    print badFn
    print $ getType badFn
    -- These two expressions should be the same
    print idExp
    print $ getType idExp
    print skk
    print $ getType skk
    -- Check typing expressions with built ins
    print onePlusOne
    print $ getType onePlusOne
    print $ getTypeInEnv builtIns onePlusOne
