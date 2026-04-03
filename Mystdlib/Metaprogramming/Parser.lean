import Lean

open Lean Parser

-- 

def print_stx_cats : IO Unit := do
  let pcats <- Lean.Parser.builtinParserCategoriesRef.get
  IO.println <| (pcats.toList |>.map Prod.fst).repr 0


inductive pcat_table_field | leadingtable | trailingtable
open IO in
def print_pcat_table_keys (nm : Name) (field : pcat_table_field) : IO Unit := do
  let pcats <- builtinParserCategoriesRef.get
  let .some pcat := pcats.find? nm | throw (.userError "no parser category with this Lean.Name")
  match field with
  | .leadingtable => println pcat.tables.leadingTable.keys
  | .trailingtable => println pcat.tables.trailingTable.keys

def pp_parse (parse_result : Array Syntax) : IO Unit := do
  IO.println <| Syntax.prettyPrint <| Syntax.node .none `anon parse_result

--

def runParserWithEmptyInit (parserfn : ParserFn) (input : String) : CoreM (Array Syntax) := do
  let env ← mkEmptyEnvironment
  let parseResult := parserfn.run (mkInputContext input "<input>")
    {env, options := {}} (getTokenTable env) (mkParserState input)
  return parseResult.stxStack.toSubarray.array

--

def wTokensTrace (p : ParserFn) : ParserFn := 
  adaptUncacheableContextFn (fun x => dbg_trace x.tokens.values; x) p

def includeTokenAux (tk : Token) (p : ParserFn) : ParserFn :=
  adaptUncacheableContextFn 
    (fun ctx => { ctx with tokens := ctx.tokens.insert tk tk}) 
    p

def includeToken (tk : Token) (p : Parser) : Parser :=
  .mk (mkAtomicInfo <| "including" ++ tk) (includeTokenAux tk p.fn)

