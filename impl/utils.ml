open Core

let add_paren_if_needed outer_priority (inner_priority, str) =
  if inner_priority < outer_priority then
    "(" ^ str ^ ")"
  else
    str

let mk_fresh_name base exclude =
  let rec search i =
    let name = base ^ string_of_int i in
    if Set.mem exclude name then
      search (i + 1)
    else
      name in
  if Set.mem exclude base then
    search 0
  else
    base


