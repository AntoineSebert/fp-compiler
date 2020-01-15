#r @"..\packages\FsLexYacc.Runtime.10.0.0\lib\net46\FsLexYacc.Runtime.dll";
#r @"bin\Debug\Machine.dll";
#r @"bin\Debug\VirtualMachine.dll";

#load "AST.fs"
#load "Parser.fs"
#load "Lexer.fs"
#load "TypeCheck.fs"
#load "CodeGen.fs"
#load "CodeGenOpt.fs"

open System
open GuardedCommands.Frontend.AST

module TestGen =
    let rand = Random()

    let indent(level: int): string =
        String.init level (fun i -> "\t")

    let rec exp_to_string (exp: Exp): string =
        match exp with
        | N n -> string n
        | B b -> if b then "true" else "false"
        | Access acc -> acc_to_string acc
        | Apply(op, [exp]) -> op + exp_to_string exp
        | Apply(op, [e1; e2]) -> "(" + exp_to_string e1 + " " + op + " " + exp_to_string e2 + ")"
        | Apply(f, es) -> ""

    and acc_to_string (acc: Access): string =
        match acc with
        | AVar name -> name
        | AIndex(acc, exp) -> acc_to_string acc + "[" + exp_to_string exp + "]"
        | ADeref exp -> exp_to_string exp + "^"

    let rec stm_to_string (stm: Stm, level: int): string =
        match stm with
        | PrintLn exp -> indent level + "print " + exp_to_string exp
        | Ass(acc, e) -> indent level + acc_to_string acc + " := " + exp_to_string e
        //| MulAssign of Access list * Exp list
        | Return opt_e -> indent level + "return"
                          + match opt_e with
                            | Some e -> " " + exp_to_string e
                            | None -> ""
        | Alt gc -> gc_to_string(gc, level)
        | Do gc -> gc_to_string(gc, level)
        | Block(decs, stms) -> " {"
                               + List.fold (fun r s -> r + s + ",\n\t")
                                           ""
                                           ([for dec in decs do dec_to_string(dec, level)]@[for stm in stms do stm_to_string(stm, level)])
                               + "}"
        | Call(name, exps) -> name
                              + "("
                              + List.fold (fun r s -> r + s + ", ")
                                          ""
                                          [for exp in exps do exp_to_string exp]
                              + ")"

    and gc_to_string (gc: GuardedCommand, level: int): string =
        match gc with
        | GC lst -> List.fold (fun r s -> r + s + ",\n")
                              ""
                              [for pair in lst do exp_to_string (fst pair) + List.fold (fun r s -> r + s + ",\n") "" [for stm in snd pair do stm_to_string(stm, level)]]

    and dec_to_string (dec: Dec, level: int): string =
        let level = level + 1
        match dec with
        | VarDec(t, s)               -> s + ": " + (type_to_string t)
        | FunDec(topt, f, decs, stm) -> if topt.IsSome then "function " else "procedure "
                                        + f
                                        + " ("
                                        + List.fold (fun r s -> r + s + ", ") "" [for dec in decs do dec_to_string(dec, level)]
                                        + ")"
                                        + if topt.IsSome then ": " + type_to_string topt.Value else ""
                                        + " ="
                                        + match stm with
                                          | Block _ -> " {\n" + stm_to_string(stm, level) + "\n" + indent level + "}"
                                          | _ -> "\n" + stm_to_string(stm, level)

    and type_to_string (_type: Typ): string =
        match _type with
        | ITyp -> "int"
        | BTyp -> "bool"
        | ATyp(subtype, opt_size) -> type_to_string(subtype) + "["
                                                        + match opt_size with
                                                          | Some(size) -> string size
                                                          | None -> ""
                                                        + "]"
        | PTyp subtype -> "*" + (type_to_string subtype)
        | FTyp(param_types, opt_ret_type) -> match opt_ret_type with
                                             | Some(subtype) -> type_to_string subtype
                                             | None -> ""
                                             + "("
                                             + List.fold (fun r s -> r + s + ", ") "" [for subtype in param_types do ((type_to_string subtype))]
                                             + ")"

    let prog_to_string (program: Program): string =
        let level = 1
        match program with
        | P(decs, stms) -> "begin\n"
                           + List.fold (fun r s -> r + s + ",\n") "" [for dec in decs do indent level + dec_to_string(dec, level)]
                           + ";\n"
                           + List.fold (fun r s -> r + s + ";\n") "" [for stm in stms do indent level + stm_to_string(stm, level)]
                           + "end"

    let join (p:Map<'a,'b>) (q:Map<'a,'b>) =
        Map(Seq.concat [ (Map.toSeq p) ; (Map.toSeq q) ])

    let get_var_by_type (scope: Map<string, Typ>, _type: Typ): Option<string> =
        let as_list = Map.filter (fun key value -> value.GetType() = _type.GetType()) scope
                      |> Map.toList

        if as_list.IsEmpty
        then None
        else Some(fst as_list.[rand.Next(as_list.Length / 2) * 2])

    let get_var (scope: Map<string, Typ>): Option<string> =
        let as_list = Map.toList scope

        if as_list.IsEmpty
        then None
        else Some(fst as_list.[rand.Next(as_list.Length / 2) * 2])

    let gen_str (scope: Map<string, Typ>): string =
        let chars = Array.concat([[|'a' .. 'z'|]; [|'A' .. 'Z'|]])
        let gen_str' =
            let sz = Array.length chars in
                String(Array.init (rand.Next(2, 10)) (fun _ -> chars.[rand.Next sz]))

        let mutable str: string = gen_str'
        while scope.ContainsKey str do
            str <- gen_str'
        str

    let rec gen_exp (scope: Map<string, Typ>): Exp =
        match rand.Next(20) with
        | 0 | 1         -> B(Convert.ToBoolean(rand.Next(2)))
        | 2 | 3         -> N(rand.Next(2048))
        | 4 | 5 | 6 | 7 -> match rand.Next(2) with
                           | 0 -> let ops = ["-"; "!"]
                                  Apply(ops.[rand.Next(ops.Length)], [gen_exp scope])
                           | _ -> let ops = ["+"; "*"; "="; "&&"; "-"; "<"; ">"; "<="; "<>"; "||"]
                                  Apply(ops.[rand.Next(ops.Length)], [gen_exp scope; gen_exp scope])
        | _             -> Access(gen_acc scope)

    and gen_acc (scope: Map<string, Typ>): Access =
        match rand.Next(15) with
        | 0 -> AIndex(gen_acc scope, gen_exp scope)
        | 1 -> ADeref(gen_exp scope)
        | _ -> match get_var scope with
               | Some(name) -> AVar(name)
               | None -> gen_acc scope
               
    let gen_param_type: Typ =
        match rand.Next(10) with
        | 0         -> ATyp((if rand.Next(2) = 1 then ITyp else BTyp), None)
        | 1 | 2 | 3 -> BTyp
        | _         -> ITyp

    let gen_typ: Typ =
       match rand.Next(20) with
       | 0 -> ATyp((if rand.Next(2) = 1 then ITyp else BTyp), Some(rand.Next(1, 64)))
       | 2 -> if rand.Next(2) = 1
              then FTyp([for i = 0 to rand.Next(4) do gen_param_type], None)
              else FTyp([for i = 0 to rand.Next(4) do gen_param_type], Some(gen_param_type))
       | 3 | 4 | 5 | 6 | 7 | 8 -> BTyp
       | _ -> ITyp

    let rec gen_stm (scope: Map<string, Typ>): Stm =
        match rand.Next(20) with
        | 0 | 1 | 2 | 3 -> PrintLn(gen_exp scope)
        | 4 -> if rand.Next(2) = 1
               then Return(None)
               else Return(Some(gen_exp scope))
        (*
        | 5 -> Alt(gen_gc scope)
        | 6 -> Do(gen_gc scope)
        | 7 -> let mutable lscope = Map.empty
               let decs = [for i = 0 to rand.Next(4) do gen_dec lscope]
               Block(decs, [for i = 0 to rand.Next(8) do gen_stm (join scope lscope)])
        | 8 | 9 | 10 -> match get_var scope with
                              | Some(name) -> Call(name, [for i = 0 to rand.Next(4) do gen_exp scope])
                              | None -> gen_stm scope
        *)
        | _ -> Ass(gen_acc scope, gen_exp scope)

    and gen_gc (scope: Map<string, Typ>): GuardedCommand =
        GC([for i = 0 to rand.Next(4) do (gen_exp scope, [for i = 0 to rand.Next(2) do gen_stm scope])])

    and gen_dec (scope: Map<string, Typ>): Dec =
       match rand.Next(8) with
       | 0 -> FunDec(
                  (if rand.Next(2) = 1 then None else Some(gen_param_type)),
                  gen_str scope,
                  [for i = 0 to rand.Next(4) do VarDec(gen_param_type, gen_str scope)],
                  gen_stm scope
              )
       | _ -> let var = VarDec(gen_typ, gen_str scope)
              printfn "%O" var.ToString
              var

    let gen_program: Program =
        let dec_count = rand.Next(4, 12)
        let stm_count = rand.Next(2, 8) * dec_count
        let mutable scope = Map.empty

        let dec_list = [for i=0 to dec_count do gen_dec scope]
        //let stm_list = [for i=0 to stm_count do gen_stm scope]

        P(dec_list, [](*stm_list*))

//printfn "%O" (TestGen.prog_to_string TestGen.gen_program)
printfn "%O" TestGen.gen_program