make a bun script that will validate that:
- all params IN CPP that are marked with b_lean_obj_arg -> IN LEAN are marked with corresponding @& too.
- all params IN IN LEAN are marked with @& -> CPP that are marked with corresponding b_lean_obj_arg too.

it should:
1. collect all cpp functions definitions (i.e. have bodies, e.g. `static inline b_lean_obj_res lean_ctor_get(b_lean_obj_arg o, unsigned i) {`)
    -> parse to {
      returnType: b_lean_obj_res | lean_obj_res | other String,
      fnName: String,
      args: Array (u_lean_obj_arg | b_lean_obj_arg | lean_obj_arg | other String)
    }
2. collect all cpp functions reexports (i.e. dont have bodies, e.g. `LEAN_EXPORT lean_obj_res lean_decode_io_error(int errnum, b_lean_obj_arg fname);`)
    -> parse to {
      returnType: b_lean_obj_res | lean_obj_res | other String,
      fnName: String,
      args: Array (u_lean_obj_arg | b_lean_obj_arg | lean_obj_arg | other String)
    }
3. print summary about functions that have same name but whose returnType or args dont match

4. collect all lean functions definitions e.g.

  @[extern "lean_string_append", expose]
  def String.append (s : String) (t : @& String) : String where

  or

  but not inside of comments e.g. like

  @[export lean_color_from_map]
  def colorValue (properties : @& Std.HashMap String String) : UInt32 :=

  and not without extern

  partial def findAux [BEq α] : @&Node α β → USize → α → Option β

  not that extern attribute can be not connected to def like in `attribute [extern "lean_mk_thunk"] Thunk.mk`

  should parse into { fnName: String, args: Array (Borrowed | NotBorrowed) }

5. print summary about
  - all params IN CPP that are marked with b_lean_obj_arg -> IN LEAN are not marked with corresponding @& too.
  - all params IN IN LEAN are marked with @& -> IN CPP are not marked with corresponding b_lean_obj_arg too.
