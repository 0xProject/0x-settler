import Lean
import EvmYul.Yul.YulNotation
import FormalYul

namespace YulImporter

open Lean

inductive ModelKind where
  | sqrt
  | sqrt512
  | cbrt
  | cbrt512
  | ln
  deriving DecidableEq, Repr

namespace ModelKind

def parse : String → Option ModelKind
  | "sqrt" => some .sqrt
  | "sqrt512" => some .sqrt512
  | "cbrt" => some .cbrt
  | "cbrt512" => some .cbrt512
  | "ln" => some .ln
  | _ => none

def namespaceName : ModelKind → String
  | .sqrt => "SqrtYul"
  | .sqrt512 => "Sqrt512Yul"
  | .cbrt => "CbrtYul"
  | .cbrt512 => "Cbrt512Yul"
  | .ln => "LnYul"

def selectorCases : ModelKind → List String
  | .sqrt => ["0x5b29048a", "0x65c9cba1"]
  | .sqrt512 => ["0x3f51628a", "0x996e33a4"]
  | .cbrt => ["0x56df2b56", "0x29f2f4f1"]
  | .cbrt512 => ["0xa83a5c08", "0x7c0352fc"]
  | .ln => ["0xef102248", "0x31d42abd"]

def functionPrefixes : ModelKind → List String
  | .sqrt =>
      ["external_fun_wrap_sqrt_", "external_fun_wrap_sqrtUp_",
       "fun_wrap_sqrt_", "fun_wrap_sqrtUp_", "fun_sqrt_", "fun_sqrtUp_", "fun__sqrt_"]
  | .sqrt512 =>
      ["external_fun_wrap_sqrt512_", "external_fun_wrap_osqrtUp_",
       "fun_wrap_sqrt512_", "fun_wrap_osqrtUp_",
       "fun__sqrt_baseCase_", "fun__sqrt_karatsubaQuotient_",
       "fun__sqrt_correction_", "fun__sqrt_babylonianStep_",
       "fun_clz_", "fun__shl256_", "fun__mul_", "fun__gt_",
       "fun__add_", "fun_toUint_", "fun_unsafeDiv_", "fun_unsafeDec_",
       "fun_and_", "fun_or_"]
  | .cbrt =>
      ["external_fun_wrap_cbrt_", "external_fun_wrap_cbrtUp_",
       "fun_wrap_cbrt_", "fun_wrap_cbrtUp_", "fun_cbrt_", "fun_cbrtUp_", "fun__cbrt_"]
  | .cbrt512 =>
      ["external_fun_wrap_cbrt512_", "external_fun_wrap_cbrtUp512_",
       "fun_wrap_cbrt512_", "fun_wrap_cbrtUp512_",
       "fun__cbrt_baseCase_", "fun__cbrt_karatsubaQuotient_",
       "fun__cbrt_quadraticCorrection_", "fun__cbrt_newtonRaphsonStep_",
       "fun_clz_", "fun__shl256_", "fun_tmp_", "fun_from_", "fun_into_"]
  | .ln =>
      ["external_fun_wrap_lnWad_", "external_fun_wrap_lnWadToRay_",
       "fun_wrap_lnWad_", "fun_wrap_lnWadToRay_", "fun_lnWad_", "fun_lnWadToRay_"]

def requiredCalls : ModelKind → List String
  | .sqrt => ["clz"]
  | .sqrt512 => ["clz", "mulmod"]
  | .cbrt => ["clz"]
  | .cbrt512 => ["clz", "mulmod"]
  | .ln => ["clz", "sdiv"]

end ModelKind

structure Options where
  kind : Option ModelKind := none
  output : Option String := none

partial def parseArgs : List String → Options → Except String Options
  | [], opts => .ok opts
  | "--kind" :: value :: rest, opts =>
      match ModelKind.parse value with
      | some kind => parseArgs rest { opts with kind := some kind }
      | none => .error s!"unknown model kind: {value}"
  | "--output" :: value :: rest, opts =>
      parseArgs rest { opts with output := some value }
  | value :: rest, opts =>
      match opts.kind, ModelKind.parse value with
      | none, some kind => parseArgs rest { opts with kind := some kind }
      | _, _ => .error s!"unexpected argument: {value}"

def sliceChars (cs : List Char) (start stop : Nat) : List Char :=
  (cs.drop start).take (stop - start)

def substrNat (src : String) (start stop : Nat) : String :=
  String.mk (sliceChars src.data start stop)

def startsWithList (cs pfx : List Char) : Bool :=
  cs.take pfx.length == pfx

def startsWithAt (cs : List Char) (i : Nat) (pat : String) : Bool :=
  startsWithList (cs.drop i) pat.data

def charAt? (cs : List Char) (i : Nat) : Option Char :=
  (cs.drop i).head?

partial def findSubstrFromChars (cs pat : List Char) (i fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      if startsWithList (cs.drop i) pat then
        some i
      else
        findSubstrFromChars cs pat (i + 1) fuel'

def findSubstrFrom (src pat : String) (start : Nat) : Option Nat :=
  findSubstrFromChars src.data pat.data start (src.data.length - start + 1)

partial def findCharFromAux (cs : List Char) (needle : Char) (i fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match charAt? cs i with
      | some c =>
          if c = needle then
            some i
          else
            findCharFromAux cs needle (i + 1) fuel'
      | none => none

def findCharFrom (cs : List Char) (needle : Char) (start : Nat) : Option Nat :=
  findCharFromAux cs needle start (cs.length - start + 1)

partial def findMatchingBraceAux (cs : List Char) (i depth fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match charAt? cs i with
      | some '{' => findMatchingBraceAux cs (i + 1) (depth + 1) fuel'
      | some '}' =>
          if depth = 1 then
            some i
          else
            findMatchingBraceAux cs (i + 1) (depth - 1) fuel'
      | some _ => findMatchingBraceAux cs (i + 1) depth fuel'
      | none => none

def findMatchingBrace (cs : List Char) (openBrace : Nat) : Option Nat :=
  findMatchingBraceAux cs openBrace 0 (cs.length - openBrace + 1)

partial def stripLineComments : List Char → List Char
  | [] => []
  | '/' :: '/' :: rest => stripLineComment rest
  | c :: rest => c :: stripLineComments rest
where
  stripLineComment : List Char → List Char
    | [] => []
    | '\n' :: rest => '\n' :: stripLineComments rest
    | _ :: rest => stripLineComment rest

partial def takeUntilCloseParen : List Char → List Char × List Char
  | [] => ([], [])
  | ')' :: rest => ([], rest)
  | c :: rest =>
      let (arg, tail) := takeUntilCloseParen rest
      (c :: arg, tail)

partial def sanitizeSolcBuiltins : List Char → List Char
  | [] => []
  | cs =>
      let memoryguard := "memoryguard(".data
      let linkersymbol := "linkersymbol(".data
      if startsWithList cs memoryguard then
        let (arg, tail) := takeUntilCloseParen (cs.drop memoryguard.length)
        arg ++ sanitizeSolcBuiltins tail
      else if startsWithList cs linkersymbol then
        let (_, tail) := takeUntilCloseParen (cs.drop linkersymbol.length)
        '0' :: sanitizeSolcBuiltins tail
      else
        match cs with
        | [] => []
        | c :: rest => c :: sanitizeSolcBuiltins rest

def normalizeYul (src : String) : String :=
  String.mk (sanitizeSolcBuiltins (stripLineComments src.data))

def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\n' || c = '\t' || c = '\r'

def isIdentChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') ||
  ('A' ≤ c && c ≤ 'Z') ||
  ('0' ≤ c && c ≤ '9') ||
  c = '_' || c = '$' || c = '.'

def skipSpaceFrom (cs : List Char) (i : Nat) : Nat :=
  i + ((cs.drop i).takeWhile isSpace).length

def readIdentFrom (cs : List Char) (i : Nat) : String × Nat :=
  let ident := (cs.drop i).takeWhile isIdentChar
  (String.mk ident, i + ident.length)

def extractDeployedCode (input : String) : Except String String := do
  let src := normalizeYul input
  let deployed ← match findSubstrFrom src "_deployed\"" 0 with
    | some i => .ok i
    | none => .error "input Yul IR does not contain a deployed object"
  let codeKw ← match findSubstrFrom src "code" deployed with
    | some i => .ok i
    | none => .error "deployed object does not contain a code block"
  let openBrace ← match findCharFrom src.data '{' codeKw with
    | some i => .ok i
    | none => .error "deployed code block has no opening brace"
  let closeBrace ← match findMatchingBrace src.data openBrace with
    | some i => .ok i
    | none => .error "deployed code block has no matching closing brace"
  .ok (substrNat src (openBrace + 1) closeBrace)

partial def splitFunctionsAux
    (src : String) (searchStart segmentStart : Nat)
    (dispatcher : String) (functions : List (String × String)) :
    Except String (String × List (String × String)) := do
  match findSubstrFrom src "function " searchStart with
  | none =>
      .ok (dispatcher ++ substrNat src segmentStart src.data.length, functions)
  | some fnStart =>
      let dispatcher := dispatcher ++ substrNat src segmentStart fnStart
      let nameStart := skipSpaceFrom src.data (fnStart + "function".length)
      let (name, _) := readIdentFrom src.data nameStart
      if name = "" then
        .error "function definition without a name"
      else
        let openBrace ← match findCharFrom src.data '{' nameStart with
          | some i => .ok i
          | none => .error s!"function {name} has no body"
        let closeBrace ← match findMatchingBrace src.data openBrace with
          | some i => .ok i
          | none => .error s!"function {name} has no matching closing brace"
        let fnSrc := substrNat src fnStart (closeBrace + 1)
        splitFunctionsAux src (closeBrace + 1) (closeBrace + 1) dispatcher
          (functions ++ [(name, fnSrc)])

def splitFunctions (src : String) : Except String (String × List (String × String)) :=
  splitFunctionsAux src 0 0 "" []

structure FunctionSource where
  name : String
  source : String
  stx : Syntax

structure ParsedContract where
  dispatcher : String
  dispatcherStx : Syntax
  functions : List FunctionSource

unsafe def loadYulParserEnv : IO Environment := do
  initSearchPath (← findSysroot)
  importModules #[{ module := `EvmYul.Yul.YulNotation, importAll := true }] {} 0 #[] false true

def parseYulStmt (env : Environment) (label src : String) : Except String Syntax :=
  match Parser.runParserCategory env `stmt src label with
  | .ok stx => .ok stx
  | .error err => .error s!"failed to parse Yul fragment {label}: {err}"

def syntaxChildren : Syntax → List Syntax
  | .node _ _ args => args.toList
  | _ => []

def identText? : Syntax → Option String
  | .ident _ raw _ _ => some raw.toString
  | _ => none

partial def firstIdent? (stx : Syntax) : Option String :=
  match stx with
  | .ident _ raw _ _ => some raw.toString
  | .node _ _ args => firstIdentInList? args.toList
  | _ => none
where
  firstIdentInList? : List Syntax → Option String
    | [] => none
    | stx :: stxs =>
        match firstIdent? stx with
        | some name => some name
        | none => firstIdentInList? stxs

partial def functionDefinitionName? (stx : Syntax) : Option String :=
  match stx with
  | .node _ kind args =>
      if kind == `EvmYul.Yul.Notation.function_definition then
        firstIdent? stx
      else
        functionDefinitionNameInList? args.toList
  | _ => none
where
  functionDefinitionNameInList? : List Syntax → Option String
    | [] => none
    | stx :: stxs =>
        match functionDefinitionName? stx with
        | some name => some name
        | none => functionDefinitionNameInList? stxs

def parseContract (env : Environment) (input : String) : Except String ParsedContract := do
  let code ← extractDeployedCode input
  let (dispatcher, rawFunctions) ← splitFunctions code
  let dispatcherStx ← parseYulStmt env "deployed dispatcher" ("{\n" ++ dispatcher ++ "\n}")
  let functions ← rawFunctions.mapM fun (splitName, source) => do
    let stx ← parseYulStmt env splitName source
    let parsedName ← match functionDefinitionName? stx with
      | some name => .ok name
      | none => .error s!"parsed Yul fragment {splitName} is not a function definition"
    if parsedName != splitName then
      .error s!"function splitter found {splitName}, but EVMYulLean parsed {parsedName}"
    else
      .ok { name := parsedName, source, stx }
  .ok { dispatcher, dispatcherStx, functions }

partial def firstNumLiteral? (stx : Syntax) : Option String :=
  match stx with
  | .node _ `num #[.atom _ lit] => some lit
  | .node _ _ args => firstNumLiteralInList? args.toList
  | _ => none
where
  firstNumLiteralInList? : List Syntax → Option String
    | [] => none
    | stx :: stxs =>
        match firstNumLiteral? stx with
        | some lit => some lit
        | none => firstNumLiteralInList? stxs

partial def calledNames (stx : Syntax) : List String :=
  let nested := (syntaxChildren stx).flatMap calledNames
  match stx with
  | .node _ kind args =>
      let here :=
        if kind == `EvmYul.Yul.Notation.function_call then
          match args.toList with
          | fn :: _ => (identText? fn).toList
          | [] => []
        else
          []
      here ++ nested
  | _ => nested

partial def caseLiterals (stx : Syntax) : List String :=
  let nested := (syntaxChildren stx).flatMap caseLiterals
  match stx with
  | .node _ kind _ =>
      let here :=
        if kind == `EvmYul.Yul.Notation.case then
          (firstNumLiteral? stx).toList
        else
          []
      here ++ nested
  | _ => nested

def contractCalledNames (contract : ParsedContract) : List String :=
  calledNames contract.dispatcherStx ++ (contract.functions.flatMap fun fn => calledNames fn.stx)

def joinLines : List String → String
  | [] => ""
  | line :: lines => lines.foldl (fun acc next => acc ++ "\n" ++ next) line

def indentBlock (pad src : String) : String :=
  joinLines ((src.splitOn "\n").map fun line => pad ++ line)

def sanitizeIdentChar (c : Char) : Char :=
  if c.isAlphanum then c else '_'

def sanitizeIdent (name : String) : String :=
  let mapped := name.map sanitizeIdentChar
  if mapped.isEmpty then "generated" else mapped

def functionDefName (name : String) : String :=
  "yulFunction_" ++ sanitizeIdent name

def renderFunctionDef (fn : FunctionSource) : String :=
  let name := fn.name
  let src := fn.source
  "def " ++ functionDefName name ++ " : EvmYul.Yul.Ast.FunctionDefinition :=\n" ++
  "  <f\n" ++
  indentBlock "  " src ++ "\n" ++
  "  >\n"

def renderFunctionInsert (fn : FunctionSource) : String :=
  let name := fn.name
  "\n  |>.insert\n" ++
  "      " ++ reprStr name ++ "\n" ++
  "      " ++ functionDefName name

def renderContract (contract : ParsedContract) : String :=
  let dispatcher := contract.dispatcher
  let functions := contract.functions
  let renderedFunctions := functions.map renderFunctionDef
  let renderedInserts := functions.map renderFunctionInsert
  "open EvmYul\n" ++
  "open EvmYul.Yul\n" ++
  "open EvmYul.Yul.Ast\n" ++
  "open scoped EvmYul.Yul.Notation\n\n" ++
  "def yulDispatcher : EvmYul.Yul.Ast.Stmt :=\n" ++
  "  <s {\n" ++
  indentBlock "    " dispatcher ++ "\n" ++
  "  }>\n\n" ++
  joinLines renderedFunctions ++ "\n" ++
  "def yulFunctions : Finmap (fun (_ : YulFunctionName) => EvmYul.Yul.Ast.FunctionDefinition) :=\n" ++
  "  (∅ : Finmap (fun (_ : YulFunctionName) => EvmYul.Yul.Ast.FunctionDefinition))" ++
  joinLines renderedInserts ++ "\n\n" ++
  "def yulContract : FormalYul.YulContract :=\n" ++
  "{\n" ++
  "dispatcher := yulDispatcher,\n" ++
  "functions := yulFunctions\n" ++
  "}\n"

def runHelpersSqrt (contractDef : String) : String :=
contractDef ++ "
def selector_sqrt : ByteArray :=
  FormalYul.bytes [0x5b, 0x29, 0x04, 0x8a]

def selector_sqrtUp : ByteArray :=
  FormalYul.bytes [0x65, 0xc9, 0xcb, 0xa1]

def run_sqrt_evm (x : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_sqrt [x]

def run_sqrt_floor_evm (x : Nat) : Except String Nat :=
  run_sqrt_evm x

def run_sqrt_up_evm (x : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_sqrtUp [x]
"

def runHelpersSqrt512 (contractDef : String) : String :=
contractDef ++ "
def selector_sqrt512 : ByteArray :=
  FormalYul.bytes [0x3f, 0x51, 0x62, 0x8a]

def selector_osqrtUp : ByteArray :=
  FormalYul.bytes [0x99, 0x6e, 0x33, 0xa4]

def run_sqrt512_wrapper_evm (xHi xLo : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_sqrt512 [xHi, xLo]

def run_osqrtUp_evm (xHi xLo : Nat) : Except String (Nat × Nat) :=
  FormalYul.callPair yulContract selector_osqrtUp [xHi, xLo]
"

def runHelpersCbrt (contractDef : String) : String :=
contractDef ++ "
def selector_cbrt : ByteArray :=
  FormalYul.bytes [0x56, 0xdf, 0x2b, 0x56]

def selector_cbrtUp : ByteArray :=
  FormalYul.bytes [0x29, 0xf2, 0xf4, 0xf1]

def run_cbrt_evm (x : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_cbrt [x]

def run_cbrt_floor_evm (x : Nat) : Except String Nat :=
  run_cbrt_evm x

def run_cbrt_up_evm (x : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_cbrtUp [x]
"

def runHelpersCbrt512 (contractDef : String) : String :=
contractDef ++ "
def selector_cbrt512 : ByteArray :=
  FormalYul.bytes [0xa8, 0x3a, 0x5c, 0x08]

def selector_cbrtUp512 : ByteArray :=
  FormalYul.bytes [0x7c, 0x03, 0x52, 0xfc]

def run_cbrt512_wrapper_evm (xHi xLo : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_cbrt512 [xHi, xLo]

def run_cbrtUp512_wrapper_evm (xHi xLo : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_cbrtUp512 [xHi, xLo]
"

def runHelpersLn (contractDef : String) : String :=
contractDef ++ "
def selector_lnWadToRay : ByteArray :=
  FormalYul.bytes [0xef, 0x10, 0x22, 0x48]

def selector_lnWad : ByteArray :=
  FormalYul.bytes [0x31, 0xd4, 0x2a, 0xbd]

def run_ln_wad_to_ray_evm (x : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_lnWadToRay [x]

def run_ln_wad_evm (x : Nat) : Except String Nat :=
  FormalYul.callWord yulContract selector_lnWad [x]
"

def runHelpers : ModelKind → String → String
  | .sqrt => runHelpersSqrt
  | .sqrt512 => runHelpersSqrt512
  | .cbrt => runHelpersCbrt
  | .cbrt512 => runHelpersCbrt512
  | .ln => runHelpersLn

def dropLeanExtension (path : String) : String :=
  if path.endsWith ".lean" then path.dropRight ".lean".length else path

def runtimeOutputPath (output : String) : String :=
  dropLeanExtension output ++ "Runtime.lean"

def proofOutputPath (output : String) : String :=
  dropLeanExtension output ++ "Proof.lean"

def moduleNameFromOutput (output : String) : String :=
  match (dropLeanExtension output).splitOn "/" |>.reverse with
  | name :: parent :: _ => parent ++ "." ++ name
  | name :: _ => name
  | [] => output

def renderRuntime (kind : ModelKind) (contract : ParsedContract) (_output : String) : String :=
  let contractDef := renderContract contract
  "import FormalYul\n" ++
  "\n" ++
  "namespace " ++ kind.namespaceName ++ "\n\n" ++
  runHelpers kind contractDef ++ "\n" ++
  "end " ++ kind.namespaceName ++ "\n"

def renderLookupLemma (fn : FunctionSource) : String :=
  let name := fn.name
  "\n@[simp]\n" ++
  "theorem lookup_" ++ sanitizeIdent name ++ " :\n" ++
  "    yulFunctions.lookup " ++ reprStr name ++ " = some " ++ functionDefName name ++ " := by\n" ++
  "  unfold yulFunctions\n" ++
  "  simp [Finmap.lookup_insert]\n"

def commaSep : List String → String
  | [] => ""
  | marker :: markers => markers.foldl (fun acc next => acc ++ ", " ++ next) marker

def namesWithPrefix (functions : List FunctionSource) (pfx : String) : List String :=
  (functions.map fun fn => fn.name).filter fun name => name.startsWith pfx

structure GeneratedAlias where
  stable : String
  original : String

def aliasFunctionDefName (stable : String) : String :=
  "yulFunction_" ++ sanitizeIdent stable

def aliasFunctionNameName (stable : String) : String :=
  "yulName_" ++ sanitizeIdent stable

def findFunction (functions : List FunctionSource) (name : String) : Except String FunctionSource :=
  match functions.find? (fun fn => fn.name = name) with
  | some fn => .ok fn
  | none => .error s!"deployed Yul has no function named {name}"

def uniqueNameWithPrefix
    (functions : List FunctionSource) (pfx : String) : Except String String :=
  match namesWithPrefix functions pfx with
  | [name] => .ok name
  | [] => .error s!"deployed Yul is missing a function with prefix {pfx}"
  | names => .error s!"deployed Yul prefix {pfx} is ambiguous: {commaSep names}"

def aliasByPrefix
    (functions : List FunctionSource) (stable pfx : String) :
    Except String GeneratedAlias := do
  let original ← uniqueNameWithPrefix functions pfx
  .ok { stable, original }

def callWithPrefixFrom
    (functions : List FunctionSource) (caller pfx : String) : Except String String := do
  let callerFn ← findFunction functions caller
  let callerCalls := calledNames callerFn.stx
  let callees := (namesWithPrefix functions pfx).filter fun name =>
    name != caller && callerCalls.contains name
  match callees with
  | [callee] => .ok callee
  | [] => .error s!"function {caller} does not call a function with prefix {pfx}"
  | names => .error s!"function {caller} has ambiguous calls with prefix {pfx}: {commaSep names}"

def aliasByCallPrefix
    (functions : List FunctionSource) (stable caller pfx : String) :
    Except String GeneratedAlias := do
  let original ← callWithPrefixFrom functions caller pfx
  .ok { stable, original }

def renderGeneratedAlias (entry : GeneratedAlias) : String :=
  "\n/-- Stable generated alias for solc-emitted function `" ++ entry.original ++ "`. -/\n" ++
  "abbrev " ++ aliasFunctionDefName entry.stable ++
    " : EvmYul.Yul.Ast.FunctionDefinition := " ++ functionDefName entry.original ++ "\n\n" ++
  "abbrev " ++ aliasFunctionNameName entry.stable ++ " := " ++ reprStr entry.original ++ "\n\n" ++
  "@[simp]\n" ++
  "theorem lookup_" ++ sanitizeIdent entry.stable ++ " :\n" ++
  "    yulFunctions.lookup " ++ aliasFunctionNameName entry.stable ++
  " = some " ++ aliasFunctionDefName entry.stable ++ " := by\n" ++
  "  unfold " ++ aliasFunctionNameName entry.stable ++ "\n" ++
  "  unfold " ++ aliasFunctionDefName entry.stable ++ "\n" ++
  "  unfold yulFunctions\n" ++
  "  simp [Finmap.lookup_insert]\n"

def generatedAliases (kind : ModelKind) (functions : List FunctionSource) :
    Except String (List GeneratedAlias) := do
  match kind with
  | .sqrt =>
      sequence [
        aliasByPrefix functions "external_fun_wrap_sqrt" "external_fun_wrap_sqrt_",
        aliasByPrefix functions "external_fun_wrap_sqrtUp" "external_fun_wrap_sqrtUp_",
        aliasByPrefix functions "fun_wrap_sqrt" "fun_wrap_sqrt_",
        aliasByPrefix functions "fun_wrap_sqrtUp" "fun_wrap_sqrtUp_",
        aliasByPrefix functions "fun_sqrt" "fun_sqrt_",
        aliasByPrefix functions "fun_sqrtUp" "fun_sqrtUp_",
        aliasByPrefix functions "fun__sqrt" "fun__sqrt_"
      ]
  | .sqrt512 =>
      let wrapSqrt512 ← uniqueNameWithPrefix functions "fun_wrap_sqrt512_"
      let wrapOsqrtUp ← uniqueNameWithPrefix functions "fun_wrap_osqrtUp_"
      let sqrt512 ← callWithPrefixFrom functions wrapSqrt512 "fun_sqrt_"
      let osqrtUp ← callWithPrefixFrom functions wrapOsqrtUp "fun_osqrtUp_"
      let sqrt256 ← callWithPrefixFrom functions sqrt512 "fun_sqrt_"
      let sqrt512Core ← callWithPrefixFrom functions sqrt512 "fun__sqrt_"
      let sqrtUp256 ← callWithPrefixFrom functions osqrtUp "fun_sqrtUp_"
      let sqrt256Core ← callWithPrefixFrom functions sqrt256 "fun__sqrt_"
      sequence [
        aliasByPrefix functions "external_fun_wrap_sqrt512" "external_fun_wrap_sqrt512_",
        aliasByPrefix functions "external_fun_wrap_osqrtUp" "external_fun_wrap_osqrtUp_",
        .ok { stable := "fun_wrap_sqrt512", original := wrapSqrt512 },
        .ok { stable := "fun_wrap_osqrtUp", original := wrapOsqrtUp },
        .ok { stable := "fun_sqrt512", original := sqrt512 },
        .ok { stable := "fun_osqrtUp", original := osqrtUp },
        .ok { stable := "fun_sqrt256", original := sqrt256 },
        .ok { stable := "fun_sqrtUp256", original := sqrtUp256 },
        .ok { stable := "fun__sqrt512", original := sqrt512Core },
        .ok { stable := "fun__sqrt256", original := sqrt256Core },
        aliasByPrefix functions "fun__sqrt_baseCase" "fun__sqrt_baseCase_",
        aliasByPrefix functions "fun__sqrt_karatsubaQuotient" "fun__sqrt_karatsubaQuotient_",
        aliasByPrefix functions "fun__sqrt_correction" "fun__sqrt_correction_",
        aliasByPrefix functions "fun__sqrt_babylonianStep" "fun__sqrt_babylonianStep_",
        aliasByPrefix functions "fun_clz" "fun_clz_",
        aliasByPrefix functions "fun__shl256" "fun__shl256_",
        aliasByPrefix functions "fun__mul" "fun__mul_",
        aliasByPrefix functions "fun__gt" "fun__gt_",
        aliasByPrefix functions "fun__add" "fun__add_",
        aliasByPrefix functions "fun_toUint" "fun_toUint_",
        aliasByPrefix functions "fun_unsafeDiv" "fun_unsafeDiv_",
        aliasByPrefix functions "fun_unsafeDec" "fun_unsafeDec_",
        aliasByPrefix functions "fun_and" "fun_and_",
        aliasByPrefix functions "fun_or" "fun_or_"
      ]
  | .cbrt =>
      sequence [
        aliasByPrefix functions "external_fun_wrap_cbrt" "external_fun_wrap_cbrt_",
        aliasByPrefix functions "external_fun_wrap_cbrtUp" "external_fun_wrap_cbrtUp_",
        aliasByPrefix functions "fun_wrap_cbrt" "fun_wrap_cbrt_",
        aliasByPrefix functions "fun_wrap_cbrtUp" "fun_wrap_cbrtUp_",
        aliasByPrefix functions "fun_cbrt" "fun_cbrt_",
        aliasByPrefix functions "fun_cbrtUp" "fun_cbrtUp_",
        aliasByPrefix functions "fun__cbrt" "fun__cbrt_"
      ]
  | .cbrt512 =>
      let wrapCbrt512 ← uniqueNameWithPrefix functions "fun_wrap_cbrt512_"
      let wrapCbrtUp512 ← uniqueNameWithPrefix functions "fun_wrap_cbrtUp512_"
      let cbrt512 ← callWithPrefixFrom functions wrapCbrt512 "fun_cbrt_"
      let cbrtUp512 ← callWithPrefixFrom functions wrapCbrtUp512 "fun_cbrtUp_"
      let cbrt256 ← callWithPrefixFrom functions cbrt512 "fun_cbrt_"
      let cbrtUp256 ← callWithPrefixFrom functions cbrtUp512 "fun_cbrtUp_"
      let cbrt512Core ← callWithPrefixFrom functions cbrt512 "fun__cbrt_"
      let cbrt512UpCore ← callWithPrefixFrom functions cbrtUp512 "fun__cbrt_"
      if cbrt512Core != cbrt512UpCore then
        .error s!"cbrt512 floor/up wrappers call different core functions: {cbrt512Core}, {cbrt512UpCore}"
      else
      let cbrt256Core ← callWithPrefixFrom functions cbrt256 "fun__cbrt_"
      let cbrt256UpCore ← callWithPrefixFrom functions cbrtUp256 "fun__cbrt_"
      if cbrt256Core != cbrt256UpCore then
        .error s!"embedded cbrt256 floor/up wrappers call different core functions: {cbrt256Core}, {cbrt256UpCore}"
      else
      sequence [
        aliasByPrefix functions "external_fun_wrap_cbrt512" "external_fun_wrap_cbrt512_",
        aliasByPrefix functions "external_fun_wrap_cbrtUp512" "external_fun_wrap_cbrtUp512_",
        .ok { stable := "fun_wrap_cbrt512", original := wrapCbrt512 },
        .ok { stable := "fun_wrap_cbrtUp512", original := wrapCbrtUp512 },
        .ok { stable := "fun_cbrt512", original := cbrt512 },
        .ok { stable := "fun_cbrtUp512", original := cbrtUp512 },
        .ok { stable := "fun_cbrt256", original := cbrt256 },
        .ok { stable := "fun_cbrtUp256", original := cbrtUp256 },
        .ok { stable := "fun__cbrt512", original := cbrt512Core },
        .ok { stable := "fun__cbrt256", original := cbrt256Core },
        aliasByPrefix functions "fun__cbrt_baseCase" "fun__cbrt_baseCase_",
        aliasByPrefix functions "fun__cbrt_karatsubaQuotient" "fun__cbrt_karatsubaQuotient_",
        aliasByPrefix functions "fun__cbrt_quadraticCorrection" "fun__cbrt_quadraticCorrection_",
        aliasByPrefix functions "fun__cbrt_newtonRaphsonStep" "fun__cbrt_newtonRaphsonStep_",
        aliasByPrefix functions "fun_clz" "fun_clz_",
        aliasByPrefix functions "fun__shl256" "fun__shl256_",
        aliasByPrefix functions "fun_tmp" "fun_tmp_",
        aliasByPrefix functions "fun_from" "fun_from_",
        aliasByPrefix functions "fun_into" "fun_into_"
      ]
  | .ln =>
      sequence [
        aliasByPrefix functions "external_fun_wrap_lnWad" "external_fun_wrap_lnWad_",
        aliasByPrefix functions "external_fun_wrap_lnWadToRay" "external_fun_wrap_lnWadToRay_",
        aliasByPrefix functions "fun_wrap_lnWad" "fun_wrap_lnWad_",
        aliasByPrefix functions "fun_wrap_lnWadToRay" "fun_wrap_lnWadToRay_",
        aliasByPrefix functions "fun_lnWad" "fun_lnWad_",
        aliasByPrefix functions "fun_lnWadToRay" "fun_lnWadToRay_"
      ]

def renderProof (kind : ModelKind) (contract : ParsedContract) (output : String) : Except String String := do
  let functions := contract.functions
  let aliases ← generatedAliases kind functions
  let runtimeModule := moduleNameFromOutput output ++ "Runtime"
  .ok <|
    "import FormalYul.Preservation\n" ++
    "import " ++ runtimeModule ++ "\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    "namespace " ++ kind.namespaceName ++ "\n\n" ++
    "/- Runtime bridge support module for the generated Yul runtime. -/\n\n" ++
    "@[simp]\n" ++
    "theorem yulContract_dispatcher : yulContract.dispatcher = yulDispatcher := rfl\n\n" ++
    "@[simp]\n" ++
    "theorem yulContract_functions : yulContract.functions = yulFunctions := rfl\n" ++
    joinLines (functions.map renderLookupLemma) ++ "\n" ++
    joinLines (aliases.map renderGeneratedAlias) ++ "\n" ++
    "end " ++ kind.namespaceName ++ "\n"

def validateSelectorCase (dispatcherStx : Syntax) (selector : String) : Except String Unit :=
  match (caseLiterals dispatcherStx).filter (fun lit => lit = selector) |>.length with
  | 1 => .ok ()
  | 0 => .error s!"deployed Yul dispatcher is missing selector case {selector}"
  | n => .error s!"deployed Yul dispatcher contains {n} selector cases for {selector}"

def validateFunctionPrefix (functions : List FunctionSource) (pfx : String) : Except String Unit :=
  match namesWithPrefix functions pfx with
  | [_] => .ok ()
  | [] => .error s!"deployed Yul is missing a function with prefix {pfx}"
  | names => .error s!"deployed Yul prefix {pfx} is ambiguous: {commaSep names}"

def validateRequiredCall (contract : ParsedContract) (name : String) : Except String Unit :=
  if (contractCalledNames contract).contains name then
    .ok ()
  else
    .error s!"deployed Yul AST has no call to required primitive/function {name}"

def validateShape (kind : ModelKind) (contract : ParsedContract) : Except String Unit := do
  for selector in kind.selectorCases do
    validateSelectorCase contract.dispatcherStx selector
  for pfx in kind.functionPrefixes do
    validateFunctionPrefix contract.functions pfx
  for call in kind.requiredCalls do
    validateRequiredCall contract call
  discard <| generatedAliases kind contract.functions

def validateInput (kind : ModelKind) (contract : ParsedContract) : Except String Unit :=
  validateShape kind contract

def usage : String :=
  "usage: yul_importer --kind <sqrt|sqrt512|cbrt|cbrt512|ln> --output <output-stem.lean> < solc-ir"

unsafe def run (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .ok opts => pure opts
    | .error err => throw <| IO.userError s!"{err}
{usage}"
  let kind ← match opts.kind with
    | some kind => pure kind
    | none => throw <| IO.userError s!"missing --kind
{usage}"
  let output ← match opts.output with
    | some output => pure output
    | none => throw <| IO.userError s!"missing --output
{usage}"
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let env ← loadYulParserEnv
  let contract ← match parseContract env input with
    | .ok contract => pure contract
    | .error err => throw <| IO.userError err
  match validateInput kind contract with
  | .ok () => pure ()
  | .error err => throw <| IO.userError err
  let runtimeText := renderRuntime kind contract output
  let proofText ← match renderProof kind contract output with
    | .ok proofText => pure proofText
    | .error err => throw <| IO.userError err
  let runtimeOutput := runtimeOutputPath output
  let proofOutput := proofOutputPath output
  IO.FS.writeFile runtimeOutput runtimeText
  IO.FS.writeFile proofOutput proofText
  IO.println s!"Generated {runtimeOutput}"
  IO.println s!"Generated {proofOutput}"
  pure 0

end YulImporter

unsafe def main (args : List String) : IO UInt32 :=
  YulImporter.run args
