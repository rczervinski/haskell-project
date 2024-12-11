-- RENAN FELIPE STRAUB CZERVINSKI, VICTOR EDUARDO SURMACZ, RENAN DE ROCCO PAMPLONA, LUCAS DE OLIVEIRA CUNHA

-- Funções relacionadas ao uso de monads ou funções que manipulam valores em um contexto monádico
-- 1. fmap
-- 2. tokenize
-- 3. parse
-- 4. Right e Left
-- 5. fmap em mapM


-- Como utilizar:
-- As variáveis proposicionais são representadas por letras maiúsculas. Elas podem ser qualquer letra de A a Z.
-- As operacoes devem ser em minusculo
-- Implicacoes e bicondicionais sao representadas por juncao de caracteres especiais
-- Exemplo: A or B,  A or not B,   A => B,   A <=> B,
-- O programa também aceita caracteres como:  ∧  ∨  ¬  →  ↔ 
-- Exemplo: A ∧ ¬B,  A → B ,  A ↔ B

-- Avisos:
-- O haskell pode não expressar os símbolos de forma correta, como  ∧  ∨  ¬  →  ↔ , ele pode aparecer como "[?]", mas os simbolos estão sendo representados de forma correta.

import Data.List (nub)

-- Definição dos tipos de dados para representar expressões proposicionais
data Prop
    = Var Char                -- Variável proposicional
    | Not Prop                -- Negação
    | And Prop Prop           -- Conjunção
    | Or Prop Prop            -- Disjunção
    | Implies Prop Prop       -- Implicação
    | Biconditional Prop Prop -- Bicondicional
    deriving (Eq, Show)

-- Tokens para o processo de parsing
data Token
    = TAnd
    | TOr
    | TNot
    | TImplies
    | TBiconditional
    | TParenOpen
    | TParenClose
    | TVar Char
    deriving (Eq, Show)


-- Tokenização
tokenize :: String -> Either String [Token]
tokenize [] = Right []
tokenize (c:cs)
    | c == '∧'                = fmap (TAnd :) (tokenize cs)
    | c == '∨'                = fmap (TOr :) (tokenize cs)
    | c == '¬'                = fmap (TNot :) (tokenize cs)
    | c == '→'                = fmap (TImplies :) (tokenize cs)
    | c == '↔'                = fmap (TBiconditional :) (tokenize cs)
    | c == '('                = fmap (TParenOpen :) (tokenize cs)
    | c == ')'                = fmap (TParenClose :) (tokenize cs)
    | take 3 (c:cs) == "and"  = fmap (TAnd :) (tokenize (drop 3 cs))
    | take 2 (c:cs) == "or"   = fmap (TOr :) (tokenize (drop 2 cs))
    | take 3 (c:cs) == "not"  = fmap (TNot :) (tokenize (drop 3 cs))
    | take 2 (c:cs) == "=>"   = fmap (TImplies :) (tokenize (drop 2 cs))
    | take 3 (c:cs) == "<=>"  = fmap (TBiconditional :) (tokenize (drop 3 cs))
    | c `elem` ['A'..'Z']     = fmap (TVar c :) (tokenize cs)
    | c == ' '                = tokenize cs
    | otherwise               = Left ("Caracter inválido: " ++ [c])

-- Parsing
parse :: [Token] -> Either String (Prop, [Token])
parse tokens = parseExpr tokens
  where
    parseExpr :: [Token] -> Either String (Prop, [Token])
    parseExpr tokens = do
        (term, rest) <- parseTerm tokens
        parseImpliesOrBiconditional term rest

    parseTerm :: [Token] -> Either String (Prop, [Token])
    parseTerm tokens = do
        (factor, rest) <- parseFactor tokens
        parseAndOr factor rest

    parseFactor :: [Token] -> Either String (Prop, [Token])
    parseFactor (TVar c : tokens) = Right (Var c, tokens)
    parseFactor (TNot : tokens) = do
        (prop, rest) <- parseFactor tokens
        Right (Not prop, rest)
    parseFactor (TParenOpen : tokens) = do
        (expr, rest) <- parseExpr tokens
        case rest of
            (TParenClose : rest') -> Right (expr, rest')
            _                     -> Left "Esperado o fechamento de parentesis"
    parseFactor _ = Left "Token inesperado"

    parseAndOr :: Prop -> [Token] -> Either String (Prop, [Token])
    parseAndOr left (TAnd : tokens) = do
        (right, rest) <- parseFactor tokens
        parseAndOr (And left right) rest
    parseAndOr left (TOr : tokens) = do
        (right, rest) <- parseFactor tokens
        parseAndOr (Or left right) rest
    parseAndOr left tokens = Right (left, tokens)

    parseImpliesOrBiconditional :: Prop -> [Token] -> Either String (Prop, [Token])
    parseImpliesOrBiconditional left (TImplies : tokens) = do
        (right, rest) <- parseExpr tokens
        Right (Implies left right, rest)
    parseImpliesOrBiconditional left (TBiconditional : tokens) = do
        (right, rest) <- parseExpr tokens
        Right (Biconditional left right, rest)
    parseImpliesOrBiconditional left tokens = Right (left, tokens)






-- avali a expressão para uma interpretação dada
evaluate :: Prop -> [(Char, Bool)] -> Bool
evaluate (Var c) env = lookup c env == Just True
evaluate (Not p) env = not (evaluate p env)
evaluate (And p q) env = evaluate p env && evaluate q env
evaluate (Or p q) env = evaluate p env || evaluate q env
evaluate (Implies p q) env = not (evaluate p env) || evaluate q env
evaluate (Biconditional p q) env = evaluate p env == evaluate q env


-- elimina implicações e bicondicionais
eliminateImplications :: Prop -> Prop
eliminateImplications (Implies p q) = Or (Not (eliminateImplications p)) (eliminateImplications q)
eliminateImplications (Biconditional p q) = And (eliminateImplications (Implies p q)) (eliminateImplications (Implies q p))
eliminateImplications (Not p) = Not (eliminateImplications p)
eliminateImplications (And p q) = And (eliminateImplications p) (eliminateImplications q)
eliminateImplications (Or p q) = Or (eliminateImplications p) (eliminateImplications q)
eliminateImplications (Var x) = Var x

-- empurra negações para dentro usando a forma normal de negação
pushNegations :: Prop -> Prop
pushNegations (Not (Not p)) = pushNegations p
pushNegations (Not (And p q)) = Or (pushNegations (Not p)) (pushNegations (Not q))
pushNegations (Not (Or p q)) = And (pushNegations (Not p)) (pushNegations (Not q))
pushNegations (Not p) = Not (pushNegations p)
pushNegations (And p q) = And (pushNegations p) (pushNegations q)
pushNegations (Or p q) = Or (pushNegations p) (pushNegations q)
pushNegations (Var x) = Var x

-- distribui disjunções sobre conjunções para obter a CNF
distribute :: Prop -> Prop
distribute (And p q) = And (distribute p) (distribute q)
distribute (Or p (And q r)) = And (distribute (Or p q)) (distribute (Or p r))
distribute (Or (And p q) r) = And (distribute (Or p r)) (distribute (Or q r))
distribute (Or p q) = Or (distribute p) (distribute q)
distribute (Not p) = Not (distribute p)
distribute (Var x) = Var x

-- retorna todas as variáveis em uma expressão
getVariables :: Prop -> [Char]
getVariables (Var x) = [x]
getVariables (Not p) = getVariables p
getVariables (And p q) = nub (getVariables p ++ getVariables q)
getVariables (Or p q) = nub (getVariables p ++ getVariables q)
getVariables (Implies p q) = nub (getVariables p ++ getVariables q)
getVariables (Biconditional p q) = nub (getVariables p ++ getVariables q)


countPositiveLiterals :: Prop -> Int
countPositiveLiterals (Var _) = 1
countPositiveLiterals (Not _) = 0
countPositiveLiterals (And p q) = countPositiveLiterals p + countPositiveLiterals q
countPositiveLiterals (Or p q) = countPositiveLiterals p + countPositiveLiterals q
countPositiveLiterals _ = 0

toCNF :: Prop -> Prop
toCNF = distribute . pushNegations . eliminateImplications

-- Converte a expressão CNF para um conjunto de cláusulas de Horn, se possível
convertToHornClauses :: Prop -> Either String [Prop]
convertToHornClauses expr =
    let cnfExpr = toCNF expr
        clauses = toClauses cnfExpr
    in if all isHornClauseSingle clauses
       then Right clauses
       else Left "\n A expressão não pode ser representada apenas com cláusulas de Horn."
       
isHornClauseHelper :: Prop -> Bool
isHornClauseHelper (Var _) = True
isHornClauseHelper (Not (Var _)) = True
isHornClauseHelper (Or p q) =
    let positiveLiterals = countPositiveLiterals (Or p q)
    in positiveLiterals <= 1 && isHornClauseHelper p && isHornClauseHelper q
isHornClauseHelper (And p q) = isHornClauseHelper p && isHornClauseHelper q
isHornClauseHelper _ = False

-- Verifica se a expressão em CNF é uma conjunção de cláusulas de Horn
isHornClause :: Prop -> Bool
isHornClause (And p q) = isHornClause p && isHornClause q
isHornClause expr = isHornClauseHelper expr

-- Divide uma expressão CNF em uma lista de cláusulas
toClauses :: Prop -> [Prop]
toClauses (And p q) = toClauses p ++ toClauses q
toClauses clause = [clause]

-- Verifica se uma cláusula é uma cláusula de Horn
isHornClauseSingle :: Prop -> Bool
isHornClauseSingle clause = countPositiveLiterals clause <= 1


-- Função auxiliar para exibir as cláusulas de Horn em duas formas: normal e LaTeX
showHornClauses :: [Prop] -> String
showHornClauses clauses = unlines $ concatMap showClause clauses
  where
    showClause clause = 
        [ "Cláusula normal: " ++ toNormal clause
        , "Cláusula em LaTeX: $$" ++ toLaTeX clause ++ "$$"
        ]
        
-- funcao para converter a expressão para o formato normal
toNormal :: Prop -> String
toNormal (Var x) = [x]
toNormal (Not p) = "¬" ++ toNormal p
toNormal (And p q) = "(" ++ toNormal p ++ " ∧ " ++ toNormal q ++ ")"
toNormal (Or p q) = "(" ++ toNormal p ++ " ∨ " ++ toNormal q ++ ")"
toNormal (Implies p q) = "(" ++ toNormal p ++ " → " ++ toNormal q ++ ")"
toNormal (Biconditional p q) = "(" ++ toNormal p ++ " ↔ " ++ toNormal q ++ ")"


-- gera todas as possíveis atribuições de valores de verdade
generateTruthAssignments :: [Char] -> [[(Char, Bool)]]
generateTruthAssignments vars = mapM (\v -> [(v, True), (v, False)]) vars

-- verifica se a expressão é uma tautologia
isTautology :: Prop -> Bool
isTautology expr = all (evaluate expr) (generateTruthAssignments (getVariables expr))

-- verifica se a expressão é uma contradição
isContradiction :: Prop -> Bool
isContradiction expr = all (not . evaluate expr) (generateTruthAssignments (getVariables expr))

-- encontra uma atribuição que satisfaz a expressão e outra que a falsifica, se contingente
findSatisfyingAndFalsifying :: Prop -> Maybe ([(Char, Bool)], [(Char, Bool)])
findSatisfyingAndFalsifying expr = 
    let assignments = generateTruthAssignments (getVariables expr)
        satisfying = filter (evaluate expr) assignments
        falsifying = filter (not . evaluate expr) assignments
    in case (satisfying, falsifying) of
        (s:_, f:_) -> Just (s, f)
        _ -> Nothing
        
-- Gera a tabela verdade para uma expressão proposicional
generateTruthTable :: Prop -> [[(Char, Bool)]]
generateTruthTable expr = 
    let vars = getVariables expr
    in generateTruthAssignments vars
        

-- Exibe a tabela verdade de uma expressão
displayTruthTable :: Prop -> IO ()
displayTruthTable expr = do
    let truthTable = generateTruthTable expr
    putStrLn "\nTabela Verdade:"
    putStrLn "Atribuição | Valor da Expressão"
    putStrLn "--------------------------"
    mapM_ (printTruthRow expr) truthTable
    putStrLn "--------------------------"

-- Exibe uma linha da tabela verdade
printTruthRow :: Prop -> [(Char, Bool)] -> IO ()
printTruthRow expr assignment = do
    let result = evaluate expr assignment
    let assignmentStr = unwords [show var ++ "=" ++ show val | (var, val) <- assignment]
    putStrLn $ assignmentStr ++ " | " ++ show result
    
-- Função para converter a atribuição para formato LaTeX
showLaTeXAssign :: [(Char, Bool)] -> String
showLaTeXAssign assign = 
    let latexAssign = map (\(var, val) -> "\\ " ++ [var] ++ " = " ++ (if val then "True" else "False")) assign
    in "$$" ++ concatMap (\s -> s ++ "") latexAssign ++ "$$"

-- Função para converter valor booleano para formato LaTeX com \text
boolToLatex :: Bool -> String
boolToLatex b = "\\text{" ++ show b ++ "}"

-- Função que gera a tabela verdade em LaTeX
generateTruthTableLatex :: Prop -> String
generateTruthTableLatex expr = 
    let vars = nub $ getVariables expr
        headers = concat (intersperse " & " (map (:[]) vars ++ ["Result"]))
        truthTable = generateTruthTable expr
        rows = map (\assignment -> 
            let values = map (boolToLatex . snd) assignment
                result = boolToLatex (evaluate expr assignment)
                row = concat (intersperse " & " (values ++ [result]))
            in row ++ " \\\\ \\hline"
            ) truthTable
        numCols = length vars + 1  
        colSpec = concat $ replicate numCols "|c" ++ ["|"]
    in "\\begin{array}{" ++ colSpec ++ "} \\hline\n" ++
       headers ++ " \\\\ \\hline\n" ++
       unlines rows ++
       "\\end{array}"

-- Função auxiliar para intercalar um elemento entre os elementos de uma lista
intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse sep (x:xs) = x : sep : intersperse sep xs

toLaTeXParen :: Prop -> String
toLaTeXParen expr@(Var _) = toLaTeX expr
toLaTeXParen expr@(Not _) = toLaTeX expr
toLaTeXParen expr = "(" ++ toLaTeX expr ++ ")"

-- converte uma expressão proposicional para o código latex correspondente
toLaTeX :: Prop -> String
toLaTeX (Var x) = [x]
toLaTeX (Not p) = "\\neg " ++ toLaTeXParen p
toLaTeX (And p q) = toLaTeXParen p ++ " \\wedge " ++ toLaTeXParen q
toLaTeX (Or p q) = toLaTeXParen p ++ " \\vee " ++ toLaTeXParen q
toLaTeX (Implies p q) = toLaTeXParen p ++ " \\to " ++ toLaTeXParen q
toLaTeX (Biconditional p q) = toLaTeXParen p ++ " \\leftrightarrow " ++ toLaTeXParen q


-- Main e interface com usuario 
main :: IO ()
main = do
    putStrLn "Digite uma expressão proposicional:"
    input <- getLine
    case tokenize input of
        Left err -> putStrLn ("Erro de tokenização: " ++ err)
        Right tokens -> case parse tokens of
            Left err -> putStrLn ("Erro de parsing: " ++ err)
            Right (expr, _) -> do
                -- Impressão da expressão original com símbolos lógicos
                putStrLn "Expressão original:"
                putStrLn (toNormal expr) 

                -- Impressão da expressão em LaTeX
                putStrLn "Expressão original em LaTeX:"
                putStrLn ("$$" ++ toLaTeX expr ++ "$$")

                -- Conversão e impressão da expressão em CNF
                let exprCNF = toCNF expr
                putStrLn "\nExpressão em CNF:"
                putStrLn (toNormal exprCNF)  
                
                -- Impressão da expressão CNF em LaTeX
                putStrLn "Expressão em CNF em LaTeX:"
                putStrLn ("$$" ++ toLaTeX exprCNF ++ "$$")

                -- Conversão para cláusulas de Horn (se aplicável)
                case convertToHornClauses exprCNF of
                    Right hornClauses -> do
                        putStrLn "\nA expressão pode ser representada como um conjunto de cláusulas de Horn:"
                        putStrLn (showHornClauses hornClauses)
                    Left message -> putStrLn message

                -- Verificação de tautologia, contradição ou contingência
                if isTautology expr
                    then do
                        putStrLn "\nA expressão é uma tautologia."
                else if isContradiction expr
                    then do
                        putStrLn "\nA expressão é uma contradição."
                else case findSatisfyingAndFalsifying expr of
                    Just (satisfying, falsifying) -> do
                        putStrLn "\nA expressão é uma contingência."
                        
                        -- Impressão das atribuições que satisfazem e falsificam a expressão
                        putStrLn "Atribuição que satisfaz a expressão:"
                        print satisfying
                        putStrLn "Em LaTeX:"
                        putStrLn (showLaTeXAssign satisfying)

                        putStrLn "\nAtribuição que falsifica a expressão:"
                        print falsifying
                        putStrLn "Em LaTeX:"
                        putStrLn (showLaTeXAssign falsifying)
                    Nothing -> putStrLn "Erro ao determinar se a expressão é uma contingência."

                -- Impressão da tabela verdade em formato normal
                displayTruthTable expr
                
                -- Impressão da tabela verdade em LaTeX
                putStrLn "\nTabela Verdade em LaTeX:"
                putStrLn (generateTruthTableLatex expr)