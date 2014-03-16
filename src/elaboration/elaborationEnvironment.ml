open Positions
open Name
open XAST
open Types
open ElaborationExceptions

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  instances    : (class_predicate * instance_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
  dictionaries : binding list; (* The dictionaries in the current context. *)
  elaborated   : bool; (* True if the expression currently analysed has already been elaborated. *)
}

let empty = { values = []; types = []; classes = []; 
  instances = []; labels = []; dictionaries = []; elaborated = false; }

let elaborated env = { env with elaborated = true }
let is_elaborated env = env.elaborated

let dictionaries env = env.dictionaries

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let bind_scheme x ts ty env =
  { env with values = (ts, (x, ty)) :: env.values }

let bind_simple x ty env =
  bind_scheme x [] ty env

let bind_type t kind tdef env =
  { env with types = (t, (kind, tdef)) :: env.types }

let lookup_type pos t env =
  try
    List.assoc t env.types
  with Not_found ->
    raise (UnboundTypeVariable (pos, t))

let lookup_type_kind pos t env =
  fst (lookup_type pos t env)

let lookup_type_definition pos t env =
  snd (lookup_type pos t env)

let lookup_class pos k env =
  try
    List.assoc (lower_tname k) env.classes
  with Not_found -> raise (UnboundClass (pos, k))

(* TODO problem of cases and class name... *)
let bind_class k c env =
  let k' = lower_tname k in
  try
    let pos = c.class_position in
    ignore (lookup_class pos k' env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    { env with classes = (k', c) :: env.classes }

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let rec is_superclass pos k1 k2 env =
  let superclasses = lookup_superclasses pos k2 env in
  List.mem k1 superclasses ||
  List.exists (fun k -> is_superclass pos k k1 env) superclasses

let lookup_instance pos class_pred env =
  try
    List.assoc class_pred env.instances
  with Not_found -> raise (UnboundInstance (pos, class_pred))

let bind_instance class_pred inst env =
  try
    let pos = inst.instance_position in
    ignore (lookup_instance pos class_pred env);
    raise (AlreadyDefinedInstance (pos, class_pred))
  with UnboundInstance _ -> 
    { env with instances = (class_pred, inst) :: env.instances }

let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let labels_of rtcon env =
  let p (_, (_, _, rtcon')) = rtcon = rtcon' in
  List.(fst (split (filter p env.labels)))

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found ->
    raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let bind_dict dict env =
  { env with dictionaries = dict :: env.dictionaries }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left (fun env (t, k) ->
    bind_type t k (primitive_type t k) env
  ) empty [
    (TName "->", KArrow (KStar, KArrow (KStar, KStar)));
    (TName "int", KStar);
    (TName "char", KStar);
    (TName "unit", KStar)
  ]

